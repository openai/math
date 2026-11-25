import OAI.LinearAlgebra.FiniteFourier.PrimeOrdinaryPencil
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedConstant
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteLabel

/-! # Action of the routed pencil on independent clock rows

Embed each shift's coefficient matrix into the clock-row bank. After
rectangle cancellation every label carries a separate copy of each query
power. Their weighted sum is precisely the ordinary pencil stage.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix
open scoped Classical

variable {ℓ m b h : ℕ} {K : Type*} [CommRing K]

/-- Place each coefficient matrix on the block with its own clock shift. -/
def routedClockMatrix [NeZero ℓ]
    (A : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K) :
    Matrix (Fin (ℓ^m * b^h)) (Fin (ℓ^m * b^h)) K :=
  let e := clockShiftRowEquivFin ℓ m b h
  fun u v =>
    let i := e.symm u
    let j := e.symm v
    if i.1 = j.1 then A i.1 i.2 j.2 else 0

theorem routedClockMatrix_mulVec [NeZero ℓ]
    (A : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K)
    (x : Fin (ℓ^m * b^h) → K) (u : Fin (ℓ^m * b^h)) :
    (routedClockMatrix A *ᵥ x) u =
      let e := clockShiftRowEquivFin ℓ m b h
      let r := e.symm u
      ∑ v, A r.1 r.2 v * x (e (r.1, v)) := by
  let e := clockShiftRowEquivFin ℓ m b h
  change (∑ i, routedClockMatrix A u i * x i) = _
  rw [← e.sum_comp]
  simp [e, Fintype.sum_prod_type, routedClockMatrix, ite_mul]

private theorem sum_units_eq_sum_erase_zero [Fact ℓ.Prime] {V : Type*} [AddCommMonoid V]
    (f : ZMod ℓ → V) :
    (∑ a : (ZMod ℓ)ˣ, f a) = ∑ a ∈ (Finset.univ : Finset (ZMod ℓ)).erase 0, f a := by
  let e : (ZMod ℓ)ˣ ≃ ↥((Finset.univ : Finset (ZMod ℓ)).erase 0) :=
    unitsEquivNeZero.trans (Equiv.subtypeEquivRight fun _ => by simp)
  exact (e.sum_comp (fun a => f a.val)).trans (Finset.sum_coe_sort _ f)

private theorem primeLabelMap_apply_pow {L X : Type} (Q : Module.End K (X → K))
    (n : ℕ) (v : L × X → K) (l : L) (x : X) :
    ((primeLabelMap (fun _ : L => Q))^n) v (l,x) = (Q^n) (fun y => v (l,y)) x := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

variable {L X : Type} [Fintype X] [Fact ℓ.Prime]
variable (Q : Fin m → Module.End K (X → K))
variable (A₀ : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K)
variable (A : (Fin m → ZMod ℓ) → Fin m → ZMod ℓ → Matrix (Fin h → Fin b) (Fin h → Fin b) K)

/-- The action of the cancelled label blocks is the actual clock pencil on the
whole label bank. The matrices `H` can be obtained in any paired coordinate charts. -/
theorem routedQueryPencilStage_action
    (H : (ZMod ℓ)ˣ → Fin m → Matrix X X K)
    (hH : ∀ (a : (ZMod ℓ)ˣ) j, H a j = ((Q j) ^ (a : ZMod ℓ).val).toMatrix')
    (x : Fin (ℓ^m * b^h) → L × X → K) (i : Fin (ℓ^m * b^h)) (p : L × X) :
    (routedClockMatrix A₀ *ᵥ (fun k => x k p)) i +
      (∑ a : (ZMod ℓ)ˣ, ∑ j, (H a j *ᵥ fun y =>
        (routedClockMatrix (fun β => A β j a) *ᵥ fun k => x k (p.1,y)) i) p.2) =
    queryPencilStage (fun j => primeLabelMap (fun _ : L => Q j)) A₀ A x i p := by
  rcases p with ⟨l,y⟩
  simp only [queryPencilStage, Pi.add_apply, Finset.sum_apply, primeLabelMap_apply_pow,
    Pi.smul_apply, smul_eq_mul, routedClockMatrix_mulVec, hH, LinearMap.toMatrix'_mulVec]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_units_eq_sum_erase_zero]

/-- A circuit for the routed matrix supplies the pencil stage needed by the
Hermite repair with the same gate count, on arbitrary independent labeled rows. -/
theorem realizesRows_routedQueryPencilStage [Fintype L]
    (H : (ZMod ℓ)ˣ → Fin m → Matrix X X K)
    (hH : ∀ (a : (ZMod ℓ)ˣ) j, H a j = ((Q j) ^ (a : ZMod ℓ).val).toMatrix') {n : ℕ}
    (hc : RealizableAtMost (routedPencilMatrix (L := L) (routedClockMatrix A₀)
      (fun (a : (ZMod ℓ)ˣ) j => routedClockMatrix (fun β => A β j a)) H) n) :
    RealizesRows (queryPencilStage (fun j => primeLabelMap (fun _ : L => Q j)) A₀ A) n := by
  simpa only [routedQueryPencilStage_action Q A₀ A H hH] using
    realizesRows_routedPencilMatrix (routedClockMatrix A₀)
      (fun (a : (ZMod ℓ)ˣ) j => routedClockMatrix (fun β => A β j a)) H hc

end

end

end FiniteFourier
end LinearAlgebra
end OAI
