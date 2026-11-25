import OAI.ThreeFlat.Diagonal.TickTotalBudget
import OAI.ThreeFlat.Diagonal.PhysicalTerminalMass
import OAI.ThreeFlat.RAM.TickTerminalRoot
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates
import OAI.ThreeFlat.Diagonal.TraceSeedResources

namespace OAI
/-! # Selected work, clock and leaf tariffs of the physical H forest -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Block

open Computability.VPVNP.BurstRAM
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u f d : ℕ}
local notation "W" => 16*u^10

/-- A saving requested after the choice of the degree-160 work bound costs 492
additional powers of the age in the H clock. The trace gate table, its actual stride
and its native slot/seed work are instantiated here for arbitrary public header size.
The later choice of a fold length does not occur in the bound. -/
theorem cursor_work_at_saving (hF : Fintype.card F≤2^W) (width : 3≤W+1)
    (ports : u≤2^(W+1)) (base : ℕ) (st : Word W)
    (S rem low total copies saving coeff unitWork : ℕ)
    (hu : 5000≤u) (gateConstant : 10^26*17^14≤u) (field : Fintype.card F≤u)
    (depth : d≤15*u^10) (fan : (copies+1)*2≤u) (unitConstant : coeff*17^6≤u)
    (native : unitWork≤coeff*(W+1)^6)
    (hk : 2≤(B.repeat (u^8)).charge+rem) (axes : (B.repeat (u^8)).charge+rem≤u^11)
    (degree : 2^(B.exponent 0)≤u) (level : B.levels+1≤u) (factors : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (clock : 2^((B.repeat (u^8)).charge+rem+low)≤2*FoldTrace.hFuel u (492+saving)) :
    let G := TraceStaticRow.gateTable hF width ports base f st u u d
    let desc := TraceSourceOwner.shape W u u u S f d G.internal
    let A := B.cursorState hk low (1+(d+d)) G.cells
    let r := (B.repeat (u^8)).run rem A
    ∀ h : r.plan.History,
      let initial := B.seedWork hk low (1+(d+d)) G.cells total copies d desc.stride G.cells
      r.rootTotal h (r.scaled unitWork (B.charges (u^8) rem A)) (fun v=>unitWork*initial v)
        ≤ FoldTrace.total u/u^saving := by
  intro G desc A r h
  have slots := TraceBitHeader.seedSlots_le (f:=f) hF width ports base st (by omega) gateConstant field depth
  have leaves := TraceBitHeader.seedTraceWork_le (S:=S) (f:=f) hF width ports base st low copies
    hu gateConstant field depth fan
  have slot160 : (1+(d+d))*G.cells*3≤u^TickTotalBudget.unitExponent :=
    slots.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have lim := B.cursor_total_work (e:=TickTotalBudget.unitExponent) (Aexp:=492+saving)
    (total:=total) (by omega) hk axes degree slot160 leaves level factors energy growth
    (TickTotalBudget.unit_work (by omega) unitConstant native) (by rw [TickTotalBudget.unit_loss]; omega) clock h
  simpa only [TickTotalBudget.unit_loss,Nat.add_sub_cancel_left] using lim


end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open RAM.HistoryTerminalTape RAM.TickTerminalRoot
open scoped BigOperators Classical

/-- Cost of the actual final native address-map and trivalent stream loop for one root.
Each endpoint belongs to an initial clipped bucket in its real destination fiber. -/
theorem terminal_native_work {F : Type} [Field F] (B : Block F) (iter rem : ℕ)
    (A : State (2^B.exponent 0) ((B.repeat iter).charge+rem))
    (h : ((B.repeat iter).run rem A).plan.History) (start pairs : A.Site→ℕ)
    (seed : ∀ a,1+A.incidentWidth a+pairs a≤ start a)
    (v : (((B.repeat iter).run rem A).plan.finish h).Site)
    (W : ℕ) (arena : RAM.TickTerminalRoot.Arena) (T : Root) (raw : ℕ→ℕ) (cap rowRate : ℕ)
    (degree : T.halves≤cap)
    (incident : (∑ i : Fin T.halves,(half T raw i.val).width)=((B.repeat iter).run rem A).terminalIncident h v)
    (endpoints : T.ext≤2*∑ a : {x // ((B.repeat iter).run rem A).plan.destination h x=v},pairs a.val)
    (privateRows : T.rows≤rowRate*((B.repeat iter).run rem A).chargeAt h (B.charges iter rem A) start v) :
    RAM.TickTerminalRoot.oneCost W arena T raw≤
      (rootFactor*(cap+4*rowRate+3))*((B.repeat iter).run rem A).chargeAt h (B.charges iter rem A) start v := by
  have floor := B.terminal_charge_covers iter rem A h start pairs seed v
  dsimp only at floor
  rw [←incident] at floor
  have measure := RAM.TickTerminalRoot.charge_covers T raw degree endpoints floor privateRows
  exact (work_bound W arena T raw).trans ((Nat.mul_le_mul_left rootFactor measure).trans_eq (Nat.mul_assoc ..).symm)


end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block

open Computability.VPVNP.BurstRAM RAM.HistoryStageBody
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u f d : ℕ}
local notation "W" => 16*u^10

noncomputable def stageUnit (u localCoeff : ℕ) :=
  10*((B.repeat (u^8)).length+2)^2*B.stageClockRate*(localCoeff*(16*u^10+1)^3)

/-- The requested saving is chosen after fixing the exponent for all native
stage work. The stage count is the actual length of the physical program. -/
theorem cursor_native_work_at_saving (hF : Fintype.card F≤2^W) (width : 3≤W+1)
    (ports : u≤2^(W+1)) (base : ℕ) (st : Word W)
    (S rem low total copies saving localCoeff : ℕ)
    (hu : 5000≤u) (gateConstant : 10^26*17^14≤u) (field : Fintype.card F≤u)
    (depth : d≤15*u^10) (fan : (copies+1)*2≤u) (fixed : (40*B.stageClockRate*localCoeff)*17^6≤u)
    (hk : 2≤(B.repeat (u^8)).charge+rem) (axes : (B.repeat (u^8)).charge+rem≤u^11)
    (degree : 2^(B.exponent 0)≤u) (level : B.levels+1≤u) (factors : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (clock : 2^((B.repeat (u^8)).charge+rem+low)≤2*FoldTrace.hFuel u (492+saving)) :
    let G:=TraceStaticRow.gateTable hF width ports base f st u u d
    let desc:=TraceSourceOwner.shape W u u u S f d G.internal
    let A:=B.cursorState hk low (1+(d+d)) G.cells
    let r:=(B.repeat (u^8)).run rem A
    ∀ h : r.plan.History,
      let initial:=B.seedWork hk low (1+(d+d)) G.cells total copies d desc.stride G.cells
      r.rootTotal h (r.scaled (B.stageUnit u localCoeff) (B.charges (u^8) rem A))
        (fun v=>B.stageUnit u localCoeff*initial v)≤FoldTrace.total u/u^saving := by
  have len : (B.repeat (u^8)).length≤u^9 := by
    rw [program_length,B.repeat_effects_length]
    exact (Nat.mul_le_mul_right _ level).trans_eq (by ring)
  have pw : u^9≤u^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have levels : (B.repeat (u^8)).length≤W := by omega
  have fifth:=StageRun.stage_rate_five (rate:=B.stageClockRate) (C:=localCoeff) levels
    (le_rfl : localCoeff*(W+1)^3≤localCoeff*(W+1)^3)
  have sixth : B.stageUnit u localCoeff≤(40*B.stageClockRate*localCoeff)*(W+1)^6 :=
    fifth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide)))
  exact B.cursor_work_at_saving hF width ports base st S rem low total copies saving _ _ hu gateConstant field
    depth fan fixed sixth hk axes degree level factors energy growth clock


end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open Computability.VPVNP.BurstRAM RAM RAM.HistoryStageBody TickTotalBudget
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u d f : ℕ}
local notation "W" => 16*u^10

/-- Row multiplier at the final typed level, including inherited private factors. -/
noncomputable def terminalRowRate (u localCoeff : ℕ) :=
  (2*(B.repeat (u^8)).length+1)*(localCoeff*(16*u^10+1)^3)

/-- One actual S43 scalar pays the earlier selected forest and the final root
stream. The real slot budget can therefore be used once for both procedures. -/
noncomputable def archiveUnit (u localCoeff degree : ℕ) :=
  B.stageUnit u localCoeff+TickTerminalRoot.rootFactor*(degree+4*B.terminalRowRate u localCoeff+3)

noncomputable def archiveConstant (localCoeff : ℕ) :=
  40*B.stageClockRate*localCoeff+TickTerminalRoot.rootFactor*(4+12*localCoeff)

theorem archiveUnit_word {degree localCoeff : ℕ} (levels : (B.repeat (u^8)).length≤W)
    (halves : degree≤(W+1)^3) :
    B.archiveUnit u localCoeff degree≤B.archiveConstant localCoeff*(W+1)^6 := by
  let z:=W+1
  have one : 1≤z:=by dsimp [z];omega
  have cubes : z^3≤z^6:=Nat.pow_le_pow_right one (by decide)
  have fourth : z^4≤z^6:=Nat.pow_le_pow_right one (by decide)
  have fifth : z^5≤z^6:=Nat.pow_le_pow_right one (by decide)
  have pos : 1≤z^6:=Nat.one_le_pow _ _ one
  have rows : B.terminalRowRate u localCoeff≤3*localCoeff*z^6:=by
    calc
      _ ≤ (3*z)*(localCoeff*z^3) := Nat.mul_le_mul_right _ (by dsimp only [z];omega)
      _ = 3*localCoeff*z^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ fourth
  have privateCost : degree+4*B.terminalRowRate u localCoeff+3≤(4+12*localCoeff)*z^6:=by
    have degreeLimit:=halves.trans cubes
    have rateLimit:=Nat.mul_le_mul_left 4 rows
    rw [Nat.add_mul]
    nlinarith
  have stage := StageRun.stage_rate_five (rate:=B.stageClockRate) (C:=localCoeff) levels
    (le_rfl : localCoeff*(W+1)^3≤localCoeff*(W+1)^3)
  have inner : B.stageUnit u localCoeff≤(40*B.stageClockRate*localCoeff)*z^6 :=
    stage.trans (Nat.mul_le_mul_left _ fifth)
  calc
    _ ≤ (40*B.stageClockRate*localCoeff)*z^6+TickTerminalRoot.rootFactor*((4+12*localCoeff)*z^6) :=
      Nat.add_le_add inner (Nat.mul_le_mul_left _ privateCost)
    _ = _ := by unfold archiveConstant;change _=(_+_)*z^6;ring

/-- The combined actual S43 cost satisfies the same age-independent degree
as the selected interior. This degree is fixed before choosing the saving. -/
theorem cursor_archive_work_at_saving (hF : Fintype.card F≤2^W) (width : 3≤W+1)
    (ports : u≤2^(W+1)) (base : ℕ) (st : Word W) (S rem low total copies saving localCoeff deg : ℕ)
    (hu : 5000≤u) (gateConstant : 10^26*17^14≤u) (field : Fintype.card F≤u)
    (depth : d≤15*u^10) (fan : (copies+1)*2≤u) (fixed : B.archiveConstant localCoeff*17^6≤u)
    (hk : 2≤(B.repeat (u^8)).charge+rem) (axes : (B.repeat (u^8)).charge+rem≤u^11)
    (degree : 2^(B.exponent 0)≤u) (halves : deg≤(W+1)^3)
    (level : B.levels+1≤u) (factors : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (clock : 2^((B.repeat (u^8)).charge+rem+low)≤2*FoldTrace.hFuel u (492+saving)) :
    let G:=TraceStaticRow.gateTable hF width ports base f st u u d
    let desc:=TraceSourceOwner.shape W u u u S f d G.internal
    let A:=B.cursorState hk low (1+(d+d)) G.cells
    let r:=(B.repeat (u^8)).run rem A
    ∀ h : r.plan.History,
      let initial:=B.seedWork hk low (1+(d+d)) G.cells total copies d desc.stride G.cells
      r.rootTotal h (r.scaled (B.archiveUnit u localCoeff deg) (B.charges (u^8) rem A))
        (fun v=>B.archiveUnit u localCoeff deg*initial v)≤FoldTrace.total u/u^saving := by
  have len : (B.repeat (u^8)).length≤u^9:=by
    rw [program_length,B.repeat_effects_length]
    exact (Nat.mul_le_mul_right _ level).trans_eq (by ring)
  have tenth : u^9≤u^10:=Nat.pow_le_pow_right (by omega) (by decide)
  exact B.cursor_work_at_saving hF width ports base st S rem low total copies saving _ _
    hu gateConstant field depth fan fixed (B.archiveUnit_word (by omega) halves)
    hk axes degree level factors energy growth clock

end

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.TraceBitHeader
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix TraceSourceOwner HistoryContraction RAM RAM.HistoryStageBody
open scoped BigOperators Classical
variable {F : Type} [Field F] [Fintype F] {w W p r k S base f q low T : ℕ}
    (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
    (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r k d
local notation "o" => 1+(d+d)
local notation "desc" => TraceSourceOwner.shape w p r k S f d (G).internal
variable (extent : 2*T≤S) (pub : ℕ→Bool)
local notation "amount" => B.seedWork hk low o (G).cells T B.cursorCopies d (desc).stride (G).cells

/-- The cost in execute_published_atom, with its current raw-code lookup,
is paid by the true S43 seed of this same site and the common stage rate. -/
theorem published_leaf_tariff (i : Fin (q+1)) (L : Lane (q+1))
    (A : HistoryInitialSeed.Layout) (z : HistoryInitialSeed.Site)
    (rows : z.rows A=(cursorAtom M t hF st B.cursorCopies T extent pub i L).table.cells)
    (endpoints : z.extPins=seedExt T low (i,L)) :
    4+42*(2*(HistoryInitialSeed.formula A).work+4)+
      (63+(4*z.rows A+z.extPins+6)*(2*(HistoryInitialSeed.rows W A).binds+4))≤
      B.stageClockRate*amount (i,L) := by
  obtain ⟨live,table,pins⟩:=native_seed_amount M t hF st B hk extent pub i L
  have rate : Physical.leafRuntimeRate ≤ B.stageClockRate := by
    unfold PhysicalStage.Block.stageClockRate
    omega
  exact (Physical.leaf_runtime_price A z _ live (rows.trans_le table) (endpoints.trans_le pins)).trans
    (Nat.mul_le_mul_right (amount (i,L)) rate)


end ThreeFlat.Diagonal.TraceBitHeader

end

end OAI
