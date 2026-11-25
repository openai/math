import OAI.Hierarchy.DescentSeedRootRows
import OAI.Hierarchy.DescentDensePhysicalOrder
import OAI.Hierarchy.DescentNetworkReindex
import OAI.Hierarchy.DescentColonies

namespace OAI
/-! # Physical site and edge codes of the original named input history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentColonies DescentInitialHost DescentSeedRoot DescentPhysicalOrder
open Computability.BorderVNP.Crossing ThreeFlat Routing Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins)
    (R s groups k : ℕ) (digits : Fin R≃Fin groups×Block k)
local notation "H₀" => initialGroup X R s
local notation "V₀" => Site X.network.copyGraph

private def groupedInputSlot (T : Type) [Fintype T] (digits : Fin R ≃ Fin groups × Block k) :
    (Σ _ : Fin R, T) ≃ Fin ((groups * Fintype.card T) * 2^k) :=
  let fields : (Σ _ : Fin R, T) ≃ (Fin groups × Fin (Fintype.card T)) × Block k :=
    ⟨fun u => (((digits u.1).1, Fintype.equivFin T u.2), (digits u.1).2),
      fun t => ⟨digits.symm (t.1.1,t.2), (Fintype.equivFin T).symm t.1.2⟩,
      fun ⟨j,v⟩ => by simp,
      fun ⟨⟨g,v⟩,x⟩ => by simp⟩
  fields.trans ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv)

private theorem ordinal_word (group vertex block vertices blocks : ℕ) :
    block + blocks * (vertex + vertices * group) = (group * vertices + vertex) * blocks + block := by
  ring

/-- Real input coordinates ordered group first, original base vertex second and radix block last. -/
def inputSlot (c : (H₀).Choice) : ((H₀).state c).graph.Site ≃ Fin ((groups*Fintype.card V₀)*2^k) :=
  groupedInputSlot R groups k V₀ digits

theorem inputSlot_val (c : (H₀).Choice) (u : ((H₀).state c).graph.Site) :
    (inputSlot X R s groups k digits c u).val=
      ((digits u.1).1.val*Fintype.card V₀+(Fintype.equivFin V₀ u.2).val)*2^k+(digits u.1).2.val :=
  ordinal_word ((digits u.1).1.val) ((Fintype.equivFin V₀ u.2).val) ((digits u.1).2.val)
    (Fintype.card V₀) (2^k)

def canonicalSite (c : (H₀).Choice) :=
  let slot:=(inputSlot X R s groups k digits c).toEmbedding.trans Fin.valEmbedding
  DescentPhysicalOrder.rename ((DescentPhysicalOrder.physical slot).toEmbedding.trans Fin.valEmbedding)

def canonicalEdge (c : (H₀).Choice) := DescentPhysicalOrder.rename ((oldOrder X c).trans Fin.valEmbedding)

def initial_world (c : (H₀).Choice) :=
  PhysicalRename.world ((H₀).state c) (canonicalSite X R s groups k digits c) (canonicalEdge X R s c)

private theorem counted_slot {T : Type} [Fintype T] {n : ℕ} (rows : T≃Fin n) (x : T) :
    (DescentPhysicalOrder.physical (rows.toEmbedding.trans Fin.valEmbedding) x).val=(rows x).val := by
  rw [DescentPhysicalOrder.physical_val,←Fin.card_Iio (rows x)]
  apply Finset.card_bij (fun t _=>rows t)
  · intro t ht;exact Finset.mem_Iio.mpr (Finset.mem_filter.mp ht).2
  · exact fun _ _ _ _ eqn=>rows.injective eqn
  · intro j hj
    refine ⟨rows.symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rows.apply_symm_apply j⟩
    change rows (rows.symm j) < rows x
    simpa using Finset.mem_Iio.mp hj

theorem canonical_site_code (c : (H₀).Choice) (u : ((H₀).state c).graph.Site) :
    DescentPacking.originalId (initial_world X R s groups k digits c).graph.Site
      (canonicalSite X R s groups k digits c u)=(inputSlot X R s groups k digits c u).val := by
  let rows:=inputSlot X R s groups k digits c
  let placed:=DescentPhysicalOrder.physical (rows.toEmbedding.trans Fin.valEmbedding)
  exact (congrArg Fin.val (DescentPhysicalOrder.code_rename (placed.toEmbedding.trans Fin.valEmbedding) u)).trans
    ((congrArg Fin.val (GroupStage.compact_dense placed.toEmbedding u)).trans (counted_slot rows u))

theorem canonical_edge_code (c : (H₀).Choice) (e : ((H₀).state c).graph.Edge) :
    DescentPacking.originalId (initial_world X R s groups k digits c).graph.Edge
      (canonicalEdge X R s c e)=((oldOrder X c) e).val :=
  (congrArg Fin.val (DescentPhysicalOrder.code_rename _ e)).trans
    (congrArg Fin.val (GroupStage.compact_dense (oldOrder X c) e))

def initial := {H₀ with state:=initial_world X R s groups k digits}

theorem initial_value : (initial X R s groups k digits).value=(H₀).value := by
  funext x
  unfold Histories.value
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg ((H₀).weight c*·) (congrFun (PhysicalRename.value ((H₀).state c) _ _) x)

theorem initial_pin (c : (H₀).Choice) (pin) : (initial_world X R s groups k digits c).graph.attach pin=
    canonicalSite X R s groups k digits c (((H₀).state c).graph.attach pin) := rfl

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
