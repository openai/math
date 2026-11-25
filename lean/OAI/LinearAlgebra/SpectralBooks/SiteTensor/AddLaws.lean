import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef

/-!
# Relabeling laws for direct sums of site tensors
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I K : Type*} [Fintype I] [AddCommMonoid K]
variable {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

private theorem pushCoeff_relabel {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) (g : X → Z) (h : ∀ x, e (f x) = g x)
    (T : X → K) (y : Y) : pushCoeff f T y = pushCoeff g T (e y) := by
  classical
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h, e.injective.eq_iff]

private theorem pushCoeff_add_apply {X Y : Type*} [Fintype X]
    (f : X → Y) (T U : X → K) (y : Y) :
    pushCoeff f (fun x => T x + U x) y = pushCoeff f T y + pushCoeff f U y :=
  congrFun (pushCoeff_add f T U) y

/-- Interchanging the two summands interchanges their tags at every site. -/
theorem sumCoeff_comm (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i ⊕ B i) :
    sumCoeff T U x = sumCoeff U T (fun i => Equiv.sumComm _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumComm (A i) (B i)
  unfold sumCoeff
  rw [add_comm]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
    (pushCoeff_relabel e _ _ (fun _ => rfl) T x)

/-- Reassociating three direct summands reassociates their tags site by site. -/
theorem sumCoeff_assoc (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (V : (∀ i, C i) → K)
    (x : ∀ i, (A i ⊕ B i) ⊕ C i) :
    sumCoeff (sumCoeff T U) V x =
      sumCoeff T (sumCoeff U V) (fun i => Equiv.sumAssoc _ _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumAssoc (A i) (B i) (C i)
  unfold sumCoeff
  simp_rw [pushCoeff_add_apply, pushCoeff_comp, add_assoc]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
    (congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
      (pushCoeff_relabel e _ _ (fun _ => rfl) V x))

/-- Adding the tensor with empty local bases on the right preserves coefficients. -/
theorem sumCoeff_zero [∀ i, IsEmpty (B i)] (T : (∀ i, A i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff T (0 : (∀ i, B i) → K) x = T (fun i => Equiv.sumEmpty _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumEmpty (A i) (B i)
  unfold sumCoeff
  rw [pushCoeff_relabel e _ (Equiv.refl _) (fun _ => rfl) T, pushCoeff_equiv]
  simp only [pushCoeff, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  rfl

/-- Adding the tensor with empty local bases on the left preserves coefficients. -/
theorem zero_sumCoeff [∀ i, IsEmpty (A i)] (U : (∀ i, B i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff (0 : (∀ i, A i) → K) U x = U (fun i => Equiv.emptySum _ _ (x i)) := by
  rw [sumCoeff_comm, sumCoeff_zero]
  rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
