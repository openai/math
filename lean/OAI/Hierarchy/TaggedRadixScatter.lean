import OAI.Hierarchy.TaggedRadixStaticNetwork
import OAI.Hierarchy.TaggedRadixStages
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Static bit scatter, trimming, and pack layout between radix stages

Each output bit uses a single trivalent equality cell with its incoming wire
or a Boolean literal. Addresses and network shape are independent of all data.
-/

namespace Hierarchy.Tagged.RadixStage
open ThreeFlat Routing
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} {I O : Type} [Fintype I] [Fintype O]

private theorem read_literal (v : I ⊕ Bool) (x : I → Bool) (y : O → Bool)
    (h : Empty → Bool) (u : Fin 0 → Bool) :
    (scatterLiteral (O := O) v).read u (fun i => Sum.elim (Sum.elim x y) h ((Fintype.equivFin _).symm i)) =
      Sum.elim x id v := by cases v <;> simp [scatterLiteral, BitSource.read]

theorem scatter_computes [CommSemiring F] (wire : StaticMap I O) :
    Computes (scatterNetwork F wire) (fun _ => 1) (staticRead wire) := by
  intro x y
  suffices every : ∀ holes : Empty → Bool, row (scatterNetwork F wire) x y holes =
      (if y = staticRead wire x then (1:F) else 0) by
    simp only [contract, every, Fintype.sum_unique, mul_one]
  intro holes
  let env : Fin (Fintype.card (Pins I O Empty)) → Bool := fun i =>
    Sum.elim (Sum.elim x y) holes ((Fintype.equivFin _).symm i)
  have cell (z : Fin 0 → Bool) (i : Fin (Fintype.card O)) : (scatterNetwork F wire).factor env z i =
      if y ((Fintype.equivFin O).symm i) = staticRead wire x ((Fintype.equivFin O).symm i) then 1 else 0 := by
    change (if env ((Fintype.equivFin _) (.inl (.inr ((Fintype.equivFin O).symm i)))) =
      (scatterLiteral (wire ((Fintype.equivFin O).symm i))).read z env then (1:F) else 0) = _
    simp only [env, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, read_literal, staticRead]
    split <;> simp_all
  have allCells (z : Fin (scatterNetwork F wire).internal → Bool) :
      (scatterNetwork F wire).weight env z = if y = staticRead wire x then 1 else 0 := by
    calc
      _ = ∏ i : Fin (Fintype.card O), if y ((Fintype.equivFin O).symm i) =
            staticRead wire x ((Fintype.equivFin O).symm i) then (1:F) else 0 := by
        unfold BitNetwork.weight
        apply Finset.prod_congr rfl
        intro i _
        exact cell z i
      _ = _ := by
        rw [← (Fintype.equivFin O).prod_comp]
        simp only [Equiv.symm_apply_apply,Fintype.prod_boole,← funext_iff]
  calc
    _ = (scatterNetwork F wire).eval env := rfl
    _ = ∑ _z : Fin (scatterNetwork F wire).internal → Bool, (if y = staticRead wire x then (1:F) else 0) := by
      unfold BitNetwork.eval
      exact Finset.sum_congr rfl (fun z _ => allCells z)
    _ = _ := by
      let z : Fin (scatterNetwork F wire).internal → Bool := fun i => Fin.elim0 i
      have points : (Finset.univ : Finset (Fin (scatterNetwork F wire).internal → Bool)) = {z} := by
        ext u
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        funext i
        exact Fin.elim0 i
      rw [points, Finset.sum_singleton]

/-- Static packing and unpacking preserve every payload bit. -/
theorem unpack_pack {r p w : ℕ} (x : RowBits (r*p) w → Bool) :
    staticRead (unpackWire (p := p)) (staticRead packWire x) = x := by
  funext row
  rcases row with ⟨i,j⟩
  simp [staticRead, packWire, unpackWire]
  exact congrArg (fun k => x (k,j)) (finProdFinEquiv.apply_symm_apply i)

theorem pack_unpack {r p w : ℕ} (x : RowBits r (p*w) → Bool) :
    staticRead (packWire (p := p)) (staticRead unpackWire x) = x := by
  funext row
  rcases row with ⟨i,j⟩
  simp [staticRead, packWire, unpackWire]
  exact congrArg (fun k => x (i,k)) (finProdFinEquiv.apply_symm_apply j)

end
end Hierarchy.Tagged.RadixStage

end OAI
