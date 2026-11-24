import OAI.Computability.VPVNP.CompressorRefreshPlacementRows
import OAI.Computability.VPVNP.CompressorRecordRefreshOldWidths
import OAI.Computability.VPVNP.PairTraversalScanDirectory

/-!
# The selected refresh's immediate-preimage directory

The binary port coordinates become part of the new base without changing
the ordinal of a position. Consequently the physical singleton rows
produced by the refresh placement worker are exactly the preimages of the
chosen mathematical term in both states' stored orders.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPlacement

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PairSimulation.LocalHistory
open PairSimulation.TraversalRows
open scoped Classical
set_option maxHeartbeats 1500000

variable {w g : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
variable (X : State S.portExponent (S.portExponent+g))

local notation "a" => S.portExponent
local notation "p₀" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
private abbrev actualPass := dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
  (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2

local notation "p" => actualPass f hf X

variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh)

private def promoted : X.network.Site ≃ ((p).next c).network.Site :=
  ((Equiv.refl X.Base).prodCongr (splitBitWord a g).toEquiv).trans (refreshPositions (bitWordFinEquiv a))

/-- A refresh placement preserves the machine's physical identifier exactly,
including the high-order promoted port and low-order residual lane fields. -/
theorem placement_identity : RepresentsPlacement (w := w) (siteOrder X) (siteOrder ((p).next c))
    ((p).step.term c).place id := by
  rintro ⟨base,lane⟩
  unfold siteWord
  apply congrArg (Fin.ofNat (2^w))
  change (bitWordFinEquiv (a+g) lane).val + 2^(a+g) * (X.baseIndex base).val =
    (bitWordFinEquiv g ((splitBitWord a g lane).2)).val + 2^g *
      ((bitWordFinEquiv a ((splitBitWord a g lane).1)).val + 2^a*(X.baseIndex base).val)
  rw [splitBitWord_number,pow_add]
  ring

theorem fiber_card_le_one (u : ((p).step.term c).output.Site) :
    Fintype.card (((p).step.term c).Preimage u) ≤ 1 := by
  apply Fintype.card_le_one_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  exact (promoted f hf X c).injective (x.property.symm.trans y.property)

theorem site_counts :
    (siteOrder X).length = X.positions ∧ (siteOrder ((p).next c)).length = X.positions := by
  have eqn {a' g' : ℕ} (Y : State a' g') : (siteOrder Y).length = Y.positions := by
    change (siteOrder Y).length = Fintype.card Y.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder Y).entries
  exact ⟨eqn _,(eqn _).trans (dyadicRefreshNext_positions X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh _ _ c)⟩

/-- The directory accepted by the traversal kernel after the selected
refresh's native singleton-table scan. It can occupy a single packed
arena with three consecutive subarrays. -/
def directory (sel : List Bool) (pub : Fin 6 → BurstRAM.Word w) (mem : Memory w) (limit : ℕ)
    (regions : RowRegions pub) (oldCount : (pub 0).val = X.positions) (newCount : (pub 2).val = X.positions)
    (capacity : (pub 4).val = 1) (below : (pub 5).val + (pub 2).val ≤ limit) :
    let v : SelectedLevel B f hf := ⟨_,_,_,_,X,p,p₀,c,sel⟩
    LevelDirectory v (after mem (eventLog (log pub 0 X.positions))) limit := by
  intro v
  have hc := site_counts f hf X c
  exact Directory.ofPhysical ((p).step.term c) (siteOrder X) (siteOrder ((p).next c)) pub _ limit
    (oldCount.trans hc.1.symm) (newCount.trans hc.2.symm) regions (by simpa only [capacity,Nat.mul_one] using below)
    id (placement_identity f hf X c) (hc.1 ▸ (collected regions oldCount newCount capacity mem).1)
    (fun v ↦ (fiber_card_le_one f hf X c v).trans_eq capacity.symm)

end CompressorRecords.RefreshPlacement

end

end VPVNP
end Computability
end OAI
