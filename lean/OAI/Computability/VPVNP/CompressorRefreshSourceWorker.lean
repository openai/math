import OAI.Computability.VPVNP.CompressorRefreshSelectorPacket
import OAI.Computability.VPVNP.CompressorSelectorSitePacket

/-! # Installing the refresh term worker at its actual calendar cut

Its demand rows are the output of the deterministic pre-selector workers. The
installed instruction table and the semantic decoder share the same finite
order, source and destination rows, field addresses and instruction budget.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.RefreshSelector

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PairSimulation.LocalHistory
open PortRefresh PortRefresh.LevelRecipe SelectedTerms NewSlots BlockPlanner DescriptorSpace
open Schedule PhaseRecipe SourceTransport ScheduledTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {g w : ℕ} (X : State S.portExponent (S.portExponent+g)) (old : IncidenceDirectory w) (start : ℕ)
local notation "O" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "sh" => RefreshBlockPlan.shape B
local notation "ord" => RefreshBlockPlan.order B
local notation "d" => LevelRecipe.Shape.ties sh
local notation "stride" => LevelRecipe.Shape.stride sh
local notation "e" => (LevelRecipe.Shape.ports sh)*(LevelRecipe.Shape.dH sh)
local notation "scr" => BlockProgram.script B
local notation "inp" => RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X)
local notation "p" => Allocation.plan X (LevelRecipe.Shape.a₀ sh) (LevelRecipe.Shape.dH sh) d stride start
local notation "source" => NewSlots.word (bits := w) (Allocation.Plan.demand p)
local notation "dest" => NewSlots.word (bits := w) (Allocation.Plan.term p)
local notation "ready" => Allocation.PrepareLayout X old (LevelRecipe.Shape.a₀ sh) (LevelRecipe.Shape.dH sh) d stride start

/-- The actual input and the explicit packet at the global selector index
satisfy every field needed for installation in the online controller. -/
theorem sourceWorker (L : DescriptorSpace.Layout) (C : Context w) (described : Describes (s := sh) inp C X start old)
    (r : ready) (low : levelStart L 0 ≤ start) (room : (p).stop < 2^w)
    (width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (cap : ℕ) (clock : TermWorker.budget B.refresh d e w X.maxWireWidth ≤ cap)
    (data : ∀ s, DemandPreparation.demandAt ord (DemandScan.rowBase X d source s) C.memory = demand s)
    (tapes : List (List Bool)) (rs : List (Report w)) :
    let W := workerInput B f hf X source dest r.demandTerm r.termRoom width cap clock C.memory data
    SelectorSite.SourceWorker W L (packet B C cap tapes rs) := by
  intro W
  have hc := counters (s := sh) inp C X start old described (.term : Stage sh)
  have hv := selector_visit B
  have code := congrArg BlockPlanner.Visit.worker hv
  have fit := limit_fits (s := sh) (w := w) (g := g) S.degree_bounds.2 X start room.le (.term : Stage sh)
  have row := workerRows B f hf X r.demandTerm r.termRoom width cap clock C.memory data
  have natural : (source).val = (p).demand := Nat.mod_eq_of_lt (by
    dsimp only [Allocation.Plan.stop,Allocation.Plan.next,Allocation.Plan.reverseSlot,Allocation.Plan.targetPort,
      Allocation.Plan.supply,Allocation.Plan.term] at room
    omega)
  have hsrc : levelStart L 0 ≤ (source).val := by
    rw [natural]; exact low.trans (Nat.le_add_right start _)
  refine ⟨code,?_,?_,termParams B f hf X old start C described,rfl,width,fun i ↦ hsrc.trans (row i).1,
    fun i ↦ ?_,fun _ _ ↦ rfl⟩
  · change ((scr).visit (selectorIndex B)).initial.eval C.pub C.state C.memory = 0
    rw [hv]; exact hc.1
  · change (((scr).visit (selectorIndex B)).stop.eval C.pub C.state C.memory).val = (O).motifCount
    rw [hv]; exact (congrArg Fin.val hc.2).trans (Nat.mod_eq_of_lt fit)
  · exact (hsrc.trans ((Nat.le_add_right ..).trans r.demandTerm)).trans (row i).2

end CompressorRecords.RefreshSelector

end

end VPVNP
end Computability
end OAI
