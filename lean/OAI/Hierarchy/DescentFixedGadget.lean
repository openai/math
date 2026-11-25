import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # Fixed local coefficient maps for the powered six-party identity -/

noncomputable section
namespace Hierarchy.DescentSixParty.PoweredGadget

open Computability.VPVNP Computability.VPVNP.WireTensor
open ThreeFlat.Diagonal.MotifKernel
open scoped BigOperators Classical

variable {F : Type*} [Field F] (G : PoweredGadget F)

/-- For each repeat count the six local matrices are fixed before any layouts
or any other matched gadgets are selected. -/
def fixedMap (z : ℕ) (hz : 0 < z) (p : Profile G.C) (j : Fin 6) :
    (MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*G.b)).Basis j →
    (MotifBase.binaryWires (k := F) supplySrc supplyDst
      (fun e => z*((p.1 e).val+G.k))).Basis j → F :=
  (G.realize z hz).choose p j

theorem fixedMap_correct (z : ℕ) (hz : 0 < z) :
    let X := MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z*G.b)
    let Y (p : Profile G.C) := MotifBase.binaryWires (k := F) supplySrc supplyDst
      (fun e => z*((p.1 e).val+G.k))
    X.coeff = ∑ p, applyLocal (G.fixedMap z hz p) (Y p).coeff :=
  (G.realize z hz).choose_spec

set_option maxHeartbeats 1600000 in
/-- Every summand of a matched collection may choose its common layout.
Its coefficient identity uses the same per-power matrices that are exposed
to the deterministic physical descriptors. -/
theorem matched_contraction_fixed {I : Type*} [Fintype I] (z : I → ℕ) (hz : ∀ i, 0 < z i) :
    let X := fun i => MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z i*G.b)
    let idx := fun (i : I) (p : Profile G.C) (e : Fin 8) => Fin (2^(z i * ((p.1 e).val + G.k)))
    ∃ layout : (I → Profile G.C) → Bool,
      (∀ p, (surviving (fun i e => z i * (((p i).1 e).val + G.k)) (layout p) : ℝ) ≤
        G.rate * (G.b * (∑ i, z i) : ℕ)) ∧
      ∀ x : ∀ i j, (X i).Basis j, (∏ i, (X i).coeff (x i)) =
        ∑ p, ∏ i, groupedTerm (A := (X i).Basis) (idx i (p i)) (layout p) (G.fixedMap (z i) (hz i) (p i)) (x i) := by
  dsimp only
  choose layout paid using fun p => G.common_layout_saving p z
  refine ⟨layout,paid,fun x => ?_⟩
  let Y (i : I) (p : Profile G.C) := MotifBase.binaryWires (k := F) supplySrc supplyDst
    (fun e => z i * ((p.1 e).val + G.k))
  calc
    _ = ∏ i, ∑ p, applyLocal (G.fixedMap (z i) (hz i) p) (Y i p).coeff (x i) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Finset.sum_apply,Y] using congrFun (G.fixedMap_correct (z i) (hz i)) (x i)
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro i _
      exact groupedAt_correct (A := (MotifBase.binaryWires (k := F) demandSrc demandDst (fun _ => z i*G.b)).Basis)
        supplySrc supplyDst (cluster (layout p)) _
        (G.fixedMap (z i) (hz i) (p i)) (x i)


end Hierarchy.DescentSixParty.PoweredGadget
end

end OAI
