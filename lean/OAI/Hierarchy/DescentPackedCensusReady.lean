import OAI.Hierarchy.DescentPackedCensusIngress

namespace OAI
/-! # Mount the physically computed census on the ordinary chooser -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentSixParty DescentPackedColony DescentSIMDLookup DescentColonies ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k G L ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ)
  (C : Layout) (b quota payload unit ratio : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "rows" => H*chunks G M
local notation "extent" => ((1+b+2*quota)*2^k)
local notation "phaseStart" => Phase.Arena.first C.chart A.degree k b (2*Phase.unit k b*M)

/-- These three numerical comparisons locate the immutable tables used by the
two chooser scans relative to the newly written census. -/
structure Apart (cut : ℕ) : Prop where
  census : Phase.CensusTables.finish C.origin extent M H G≤cut ∨ C.source.base+rows≤C.origin
  phase : phaseStart≤cut ∨ C.source.base+rows≤C.chart.origin
  roster : C.chart.roster.base+H*A.degree≤cut ∨ C.source.base+rows≤C.chart.roster.base

theorem Setup.accept (rs : DynamicSplit.Roster ℓ A.degree) (m o : Memory w) (cut : ℕ)
    (prev : Setup (G:=G) A hosts hv C b quota payload unit ratio rs m)
    (areas : Apart (G:=G) (ℓ:=ℓ) A C b quota payload unit cut)
    (frame : ∀i,i<cut ∨ C.source.base+rows ≤ i → o i=m i)
    (slots : A.PortOrder quota) (passed : Reads C.source (A.rawCensus (GroupStage.plane hosts hv) groups slots b) M o) :
    Ready A groups hosts hv C b quota payload unit ratio rs o := by
  refine ⟨?_,slots,passed⟩
  refine {toGeometry:=prev.toGeometry,censusROM:=?_,phaseROM:=?_,stored:=?_}
  · intro a lo hi
    change C.origin≤a at lo
    change a<Phase.CensusTables.finish C.origin extent M H G at hi
    exact (frame a (areas.census.imp (fun h=>hi.trans_le h) (fun h=>h.trans lo))).trans (prev.censusROM a lo hi)
  · intro a lo hi
    change C.chart.origin≤a at lo
    change a<phaseStart at hi
    exact (frame a (areas.phase.imp (fun h=>hi.trans_le h) (fun h=>h.trans lo))).trans (prev.phaseROM a lo hi)
  · intro v i
    have next := Nat.mul_le_mul_right A.degree v.isLt
    rw [Nat.succ_mul] at next
    have bound : v.val*A.degree+i.val<H*A.degree := by have := i.isLt;omega
    exact (frame _ (areas.roster.imp (fun h=>(Nat.add_lt_add_left bound _).trans_le h)
      (fun h=>h.trans (Nat.le_add_right ..)))).trans (prev.stored v i)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser

end OAI
