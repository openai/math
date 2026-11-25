import OAI.ThreeFlat.Diagonal.TraceRepeatedAdmission
import OAI.Hierarchy.TraceIterationPlacement
import OAI.Hierarchy.TraceIterationClock
import OAI.ThreeFlat.Diagonal.TraceStageConstants
import OAI.Hierarchy.TraceNativePorts

namespace OAI
/-! # The actual native history loop at the grid width

One fixed compressor and its alphabet choose the executable block before any input
is seen. The public directory and the supplied polynomial slot ceiling give uniform word
and time bounds for the exact machine, including early rejection of a malformed record.
-/
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure TraceDistribution Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem valid_cast {d l l' K W : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) {sizes : List ℕ} (q : Program.RecordTable r K W sizes)
    (raw : List Bool) :
    ((Program.recast e A r).plan.read (Program.changeTable e A r q).codes raw).isSome =
      (r.plan.read q.codes raw).isSome := by cases e;rfl

/-- A public prefix width, schedule length and seeded layout determine the
native ROM and the record table used in both branch selection and parsing. -/
def ControllerAt (w k n offs slots : ℕ) (hk : 2≤k+1) (fits : B.blockCharge*n≤k+1) : Prop :=
    ∀ (arch : Archive) (β edges : ℕ) (cur ctr : Word (64*w)) (field : FieldCode F (64*w))
      (atBase : ArchivePlacement arch β w) (ptr : cur.val=arch.control) (counter : cur.val<ctr.val)
      (alphabet : arch.K=B.alphabetCap) (bits : ℕ→Bool) (origin : Memory (64*w)),
      let P:=B.repeat n
      let rem:=k+1-P.charge
      let e : k+1=P.charge+rem := by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) offs slots
      let A : State (2^B.exponent 0) (P.charge+rem):=e ▸ X
      let steps:=P.directory rem (k+1)
      let raw:=List.ofFn (fun j : Fin (2^(3*w/5))=>bits j.val)
      let r:=Physical.run B hk (w/2) offs slots n fits
      let loop:=NavigationPass.repeated cur ctr arch.K B
      ∃ hword : B.repeatFactor*(X.maxWidth+1)*B.widthBase^n<2^(64*w),
        let table:=physicalTable B hk (w/2) offs slots n (64*w) fits hword
        TickStageSpec.Admission field loop.block loop.publicData
          (fun m=>m=origin ∧ arch.Visit steps edges bits cur [] X m ∧ (m ctr.val).val=n)
          (fun _=>(r.plan.read table.codes raw).isSome)
          (fun _ out=>arch.TraceJournal (2^w) cur ctr P rem A arch.cursor raw origin out ∧
            ∃ v : Run.WireLayer,(P.run rem A).EndsAt
              (B.recordTable B.alphabetCap (64*w) n rem A le_rfl
                (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact hword)).records
              raw v (raw.drop (64*w*arch.histWords steps)) ∧ arch.Visit steps edges bits cur steps v.state out)
          (2^(3*w/5))

/-- The native installed loop tests precisely the records of the same table used by
the selector and leaves the terminal physical graph and complete stage journal. -/
theorem native_repeated_controller {u s : ℕ→ℕ} (scale : Scale u s) (a b : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {k} (hk : 2≤k+1) (_axes : k+1=u w+1-w/2) (offs slots : ℕ)
      (_ports : offs*slots*3≤a*(w+1)^b) (fits : B.blockCharge*s w≤k+1),
      ControllerAt B w k (s w) offs slots hk fits := by
  filter_upwards [eventual_iteration_limits B scale,eventual_iteration_clock B scale B.alphabetCap,
    TraceStageConstants.eventual B,multiplicity_small scale 1 a b B.widthBase,
    multiplicity_room scale B.repeatFactor a b B.widthBase,eventually_ge_atTop 7] with w limits time constants small enough hw
  intro k hk _axes offs slots _ports fits arch β edges cur ctr field atBase ptr counter alphabet bits origin
    P rem e X A steps raw r loop
  have init : X.maxWidth≤2^(w/2)*(a*(w+1)^b) := X.maxWidth_le fun i=>by
    rw [B.cursorState_width];exact Nat.mul_le_mul_left _ _ports
  have trueZ := Nat.mul_le_mul_right (B.widthBase^(s w)) (Nat.add_le_add_right init 1)
  have word : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^(64*w) := by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left _ trueZ).trans_lt enough
  refine ⟨word,?_⟩
  intro table
  have same : A.maxWidth=X.maxWidth := State.maxWidth_cast_lanes e X
  have base : Fintype.card A.Base=k+1 := (Program.baseCast e X).trans (Fintype.card_fin _)
  let z := (A.maxWidth+1)*B.widthBase^s w
  have wordZ : B.repeatFactor*z<2^(64*w) := by dsimp only [z];rw [same,←Nat.mul_assoc];exact word
  have tiny : z≤(2^w)^4 := by
    dsimp only [z];rw [same,←pow_mul]
    exact (trueZ.trans (by simpa only [one_mul] using small)).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have reach : (P.run rem A).WidthCeiling z := B.repeat_widthCeiling (s w) rem A
  have rule : ∀ d∈P.recordBounds,d.1≤arch.K ∧ d.2*z<2^(64*w) := by
    intro d hd
    rw [alphabet]
    exact ⟨Block.component_le Prod.fst (B.bounds_repeat _ hd),
      (Nat.mul_le_mul_right z (Block.component_le Prod.snd (B.bounds_repeat _ hd))).trans_lt wordZ⟩
  have hspace : arch.TraceLimits (2^w) cur (P.directory rem (Fintype.card A.Base)) edges (2^(3*w/5)) := by
    rw [base]
    simpa only [P,rem,_axes] using limits (_axes ▸ fits) arch β edges cur alphabet atBase ptr
  let canonical := B.recordTable B.alphabetCap (64*w) (s w) rem A le_rfl wordZ
  have sameRead (K : ℕ) (hk' : K=B.alphabetCap)
      (hb : ∀ d∈P.recordBounds,d.1≤K ∧ d.2*z<2^(64*w)) :
      ((P.run rem A).plan.read canonical.codes raw).isSome =
      ((P.run rem A).plan.read (P.table K (64*w) z hb rem A reach).codes raw).isSome := by
    subst K;rfl
  have sameEnd (K : ℕ) (hk' : K=B.alphabetCap)
      (hb : ∀ d∈P.recordBounds,d.1≤K ∧ d.2*z<2^(64*w)) (v : Run.WireLayer) (xs : List Bool) :
      (P.run rem A).EndsAt (P.table K (64*w) z hb rem A reach).records raw v xs →
        (P.run rem A).EndsAt canonical.records raw v xs := by
    subst K;exact id
  intro labels registers machineSlots machine
  refine TickStageSpec.Admission.mono
    (fun {labels registers machineSlots} M =>
      arch.run_trace_repeated B (s w) rem A field cur ctr edges (2^(3*w/5)) z bits origin
        (by omega) (TraceRetainedRoom.native hw) (by rw [alphabet];exact constants.1)
        counter rule reach tiny (constants.2 (s w)) hspace M) ?_ ?_ ?_ ?_ machine
  · rintro m ⟨hm,visit,cnt⟩
    exact ⟨hm,by simpa only [base] using visit.cast e,cnt⟩
  · intro m _
    have hx := (valid_cast e X (P.run rem A) canonical raw).trans (sameRead arch.K alphabet rule)
    exact (congrArg (fun b : Bool=>b=true) hx).to_iff
  · intro m out _ _ hit
    rcases hit with ⟨journal,v,parsed,visit⟩
    refine ⟨journal,v,?_,?_⟩
    · let remaining (card : ℕ) := raw.drop (64*w*arch.histWords (P.directory rem card))
      have endAt : (P.run rem A).EndsAt canonical.records raw v (remaining (Fintype.card A.Base)) :=
        sameEnd arch.K alphabet rule v _ parsed
      exact (congrArg (fun suffix => (P.run rem A).EndsAt canonical.records raw v suffix)
        (congrArg remaining base)).mp endAt
    · simpa only [base] using visit
  · rw [base]
    simpa only [alphabet,_axes,P,rem] using time (_axes ▸ fits) cur arch.cursor

/-- Uniform over every machine architecture admitted by the actual trace model. -/
theorem native_machine_controller [Fintype F] {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words : ℕ}, pc≤64*w → regs≤64*w → words≤64*w →
      ∀ {k : ℕ} (hk : 2≤k+1) (_axes : k+1=u w+1-w/2)
        (M : Machine (64*w) pc regs words) {N base fuel : ℕ}
        (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel) (q : Fintype.card F≤2^(64*w))
        (st : Word (64*w)) (runs : B.blockCharge*s w≤k+1),
        let slots := (TraceStaticRow.gateTable q fit.width fit.labels base fuel st regs words ((k+1)+w/2)).cells
        let offsets := 1+(((k+1)+w/2)+((k+1)+w/2))
        ControllerAt B w k (s w) offsets slots hk runs := by
  filter_upwards [native_repeated_controller B scale (3*5*10^26*65^14) 15,
    eventual_native_port_count (F:=F) scale] with w replay ports
  intro pc regs words hp hr hw k hk _axes M N base fuel fit q st runs slots offs
  exact replay hk _axes offs slots (ports hp hr hw _axes M fit q st) runs


end
end Hierarchy.TraceAdmission

end OAI
