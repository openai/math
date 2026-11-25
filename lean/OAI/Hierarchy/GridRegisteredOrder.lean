import OAI.Hierarchy.GridRegisteredSetting
import OAI.ThreeFlat.Diagonal.TraceArchiveSource
import OAI.Hierarchy.TraceSeedDirectories
import OAI.ThreeFlat.Diagonal.PhysicalSeedLayer
import OAI.ThreeFlat.Diagonal.TraceResourceDimensions

namespace OAI
/-! # The fixed physical register order in the selected grid

The public root count depends only on the block schedule and the initial
number of axes. Registration gives the same terminal ordinal, lane ancestor
and charge that the occurrence and geometry publishers read.
-/

namespace Hierarchy.GridRegisteredOrder
open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution TraceAdmission GridRegisteredSetting
open NavigationPass NavigationDirectory RAM.NavigationNodeRows
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base fuel axes low : ℕ}
variable (D : RunData F W pc regs words S base fuel axes low)

def rootCount : ℕ :=
  let P := D.block.repeat D.passes
  P.finalSites (axes+1-P.charge) (axes+1)

omit [Fintype F] in
private theorem recast_card {d l l' N : ℕ} (e : l=l') (X : State d l)
    (r : Run F (e ▸ X : State d l'))
    (fixed : ∀ z,Fintype.card (r.plan.finish z).Site=N) :
    ∀ z,Fintype.card ((Program.recast e X r).plan.finish z).Site=N := by
  cases e
  exact fixed

/-- The structural terminal count holds for every history of the native run. -/
theorem roots_fixed (h : D.run.plan.History) : D.roots h = rootCount D := by
  let P := D.block.repeat D.passes
  let rem := axes+1-P.charge
  let dep := axes+1+low
  let gates := TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs words dep
  let X := D.block.cursorState D.axesFit low (1+(dep+dep)) gates.cells
  have eqn : axes+1=P.charge+rem := by
    have room := D.passesFit
    dsimp [P,rem]
    rw [D.block.charge_repeat]
    omega
  let Y : State (2^D.block.exponent 0) (P.charge+rem) := eqn ▸ X
  have size : @Fintype.card Y.Base Y.finiteBase=axes+1 :=
    (Program.baseCast eqn X).trans (Fintype.card_fin (axes+1))
  refine recast_card (N:=rootCount D) eqn X (P.run rem Y) (fun z => ?_) h
  exact (P.finalSites_card rem Y z).trans (congrArg (P.finalSites rem) size)

omit [Fintype F] in
/-- The terminal layer produced by the numeric directory has the same count
as the recurrence on the typed block. The cursor and all its bank addresses
are arbitrary. -/
theorem directory_count {degree : ℕ} (P : Program F degree) (K rem v : ℕ)
    (c : Cursor) (layer : Layer) (initial : layer.count=v*2^(P.charge+rem)) :
    (TraceRecovery.lastLayer K (P.directory rem v) c layer).count=P.finalSites rem v := by
  induction P generalizing c layer v with
  | done => simpa only [Program.charge,Nat.zero_add,Program.directory,TraceRecovery.lastLayer,
      Program.finalSites] using initial
  | shrink s t T small tail ih =>
    let tag := 2^CompressorPacking.tagBits (2^s)
    let x : CompressorPacking.Native.ShrinkStage.Dimensions :=
      ⟨v,2^s,2*2^s+1,tag,2^(tail.charge+rem),2^t⟩
    let op := Stage.shrink x
    exact ih (v:=v*tag) (c:=(allocate K c op).next) (layer:=nodeLayer K c op) rfl
  | refresh s t height pad coeff γ C T two pos sym grade zero conn deg tail ih =>
    let op := Stage.refresh v (2^s) (2^(tail.charge+rem)) height pad
    have sizes := Program.refresh_positions s (tail.charge+rem) v height pad
    exact ih (v:=v*2^s) (c:=(allocate K c op).next) (layer:=nodeLayer K c op)
      (sizes.1.trans sizes.2.symm)

/-- The roots of every selected history equal the public terminal directory
count. This equality holds even before the registration program executes. -/
theorem roots_archive (w off slots cap static : ℕ) (h : D.run.plan.History) :
    let a := TraceSeedWriter.archive D.block w (axes+1) off slots cap static
    let P := D.block.repeat D.passes
    D.roots h=(TraceRecovery.lastLayer a.K (P.directory (axes+1-P.charge) (axes+1))
      a.cursor a.seedLayer).count := by
  intro a P
  rw [roots_fixed]
  symm
  apply directory_count P
  have room := D.passesFit
  have charge : P.charge≤axes+1 := by simpa only [P,D.block.charge_repeat] using room
  rw [show P.charge+(axes+1-P.charge)=axes+1 by omega]
  rfl

/-- A single admitted receipt identifies the public final layer's count for
every selector, so the same publication program serves all accepted histories. -/
theorem roots_eq_last {N : ℕ} (accepted : D.run.plan.History) (count : D.roots accepted=N)
    (h : D.run.plan.History) : D.roots h=N :=
  (roots_fixed D h).trans ((roots_fixed D accepted).symm.trans count)

/-- The address fields come from the actual grid rows. All six scalar
dimensions are chosen before the first selector bit is read. -/
def fixed (_D : RunData F W pc regs words S base fuel axes low) (template : Resources.Parameters ℕ) (N m n B : ℕ) : Resources.Parameters ℕ :=
  { template with
    lanes := 2^(axes+1)
    roots := N
    directions := m+1
    pairSpan := 2^low
    band := GridIdleLayout.each m n B
    cap := S }

theorem fixed_eq (template : Resources.Parameters ℕ) {N : ℕ} (m n B : ℕ)
    (h : D.run.plan.History) (count : D.roots h=N) :
    fixed D template N m n B = D.parameters template h m n B := by
  subst N
  rfl

/-- Transporting a terminal ordinal changes only the bound on its natural
index. This is also the ordinal used for the already published ancestor word. -/
theorem ordinal {N : ℕ} (h : D.run.plan.History) (count : D.roots h=N)
    (v : (D.run.plan.finish h).Site) :
    Resources.indexEquiv D.run h count v = Fin.cast count (D.ordinal h v) := rfl

/-- Registration uses the physical initial lane and terminal numbering from
the admitted machine. Once the public row count is identified, the receipt is
precisely the one consumed by the selected pin distributor. -/
theorem registered (template : Resources.Parameters ℕ) (h : D.run.plan.History) (C : D.run.Charges)
    (unit m n B : ℕ) {N owners dst : ℕ} (count : D.roots h=N) {mem : Memory W}
    (receipt :
      let idx := Resources.indexEquiv D.run h count
      Resources.Registered owners dst (fixed D template N m n B)
        (fun j => idx (D.run.plan.destination h (GridPhysicalAdmission.initialLane (Nat.succ_pos axes) j)))
        (fun v => unit*D.run.chargeAt h C
          (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) (idx.symm v)) mem) :
    Resources.Registered owners dst (D.parameters template h m n B) (D.dest h) (D.work h C unit) mem := by
  subst N
  exact receipt

/-- Read both banks by the semantic grid ordinals in the same incoming memory. -/
theorem reads (template : Resources.Parameters ℕ) (h : D.run.plan.History) (C : D.run.Charges)
    (unit m n B : ℕ) {owners dst : ℕ} {mem : Memory W}
    (rows : Resources.Registered owners dst (D.parameters template h m n B) (D.dest h) (D.work h C unit) mem) :
    (∀ j : Fin (2^(axes+1)), mem (owners+j.val)=((D.dest h j).val : Word W)) ∧
    ∀ (v : Fin (D.roots h)) (col : Fin ((m+1)+2)),
      (mem (dst+v.val*((m+1)+2)+col.val)).val = D.costs template h m n B C unit v col :=
  ⟨rows.owners,Resources.Registered.cost_read _ _ _ rows⟩

end
end Hierarchy.GridRegisteredOrder

end OAI
