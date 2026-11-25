import OAI.LinearAlgebra.SpectralBooks.SpectralSpace
import OAI.LinearAlgebra.SpectralBooks.WireSymmetry
import Mathlib.Tactic.FinCases

/-!
# Moving one index along an identity wire

For two placements differing only at one index, its old site contracts that
index with the first end of a wire of the same dimension. Its new site reads
the second end of the wire. The equality of the two wire labels recovers
exactly the coefficients of the original tensor at the new placement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped Classical BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

private theorem diagonal_pair_coeff {D : Type*} [Fintype D] (z : Fin 2 → D) :
    (diagonal (Fin 2) K D).coeff z = if z 0 = z 1 then 1 else 0 := by
  classical
  have he (a : D) : (z = fun _ => a) ↔ z 0 = a ∧ z 1 = a := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · intro h
      funext i
      fin_cases i <;> simp [h]
  unfold diagonal
  dsimp only
  rw [Finset.sum_eq_single (z 0)]
  · simp only [he, true_and, eq_comm]
  · intro a _ ha
    exact ite_eq_right (fun h => ha ((he a).mp h).1.symm)
  · simp

/-- Moving a single index between two placed tensors is a local restriction
after tensoring with the two-site diagonal of that index dimension. -/
theorem move_restricts_with_wire (T : Raw I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) :
    (T.group q).Restricts ((T.group p).mul ((diagonal (Fin 2) K (T.Leg i₀)).group
      ![p i₀, q i₀])) := by
  classical
  let loc : Fin 2 → J := ![p i₀, q i₀]
  let W := (diagonal (Fin 2) K (T.Leg i₀)).group loc
  let S := (T.group p).mul W
  let ok (j : J) (x : (T.group q).Leg j) (y : S.Leg j) : Prop :=
    (∀ (i : I), i ≠ i₀ → ∀ (h : p i = j) (h' : q i = j),
      y.1 ⟨i, h⟩ = x ⟨i, h'⟩) ∧
    (∀ h : p i₀ = j, y.1 ⟨i₀, h⟩ = y.2 ⟨0, h⟩) ∧
    (∀ h : q i₀ = j, y.2 ⟨1, h⟩ = x ⟨i₀, h⟩)
  refine ⟨fun j x y => if ok j x y then 1 else 0, ?_⟩
  intro x
  let v (i : I) := x (q i) ⟨i, rfl⟩
  let keep (j : J) : S.Leg j := (fun i => v i.val, fun _ => v i₀)
  have hok (j : J) : ok j (x j) (keep j) := by
    refine ⟨?_, fun _ => rfl, ?_⟩
    · rintro i _ h rfl
      rfl
    · rintro rfl
      rfl
  have hcoeff (y : ∀ j, S.Leg j) : S.coeff y =
      T.coeff (fun i => (y (p i)).1 ⟨i, rfl⟩) *
        (if (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩ then 1 else 0) :=
    congrArg (_ * ·) (diagonal_pair_coeff (fun k => (y (loc k)).2 ⟨k, rfl⟩))
  change T.coeff v = ∑ y : ∀ j, S.Leg j, S.coeff y * ∏ j, if ok j (x j) (y j) then 1 else 0
  have hp (y : ∀ j, S.Leg j) : (∏ j, if ok j (x j) (y j) then (1 : K) else 0) =
      if ∀ j, ok j (x j) (y j) then 1 else 0 := Fintype.prod_boole
  simp_rw [hp]
  rw [Finset.sum_eq_single keep]
  · rw [hcoeff keep]
    have hw : (keep (p i₀)).2 ⟨0, rfl⟩ = (keep (q i₀)).2 ⟨1, rfl⟩ := rfl
    rw [ite_eq_left hw, ite_eq_left hok, mul_one, mul_one]
  · intro y _ hy
    by_cases hc : ∀ j, ok j (x j) (y j)
    · by_cases hw : (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩
      · exfalso
        apply hy
        have hright : (y (q i₀)).2 ⟨1,rfl⟩ = v i₀ := (hc _).2.2 rfl
        have hleft := hw.trans hright
        funext j
        apply Prod.ext
        · funext ⟨i, hi⟩
          subst j
          by_cases h : i = i₀
          · subst i
            exact ((hc _).2.1 rfl).trans hleft
          · have transport (j : J) (hj : q i = j) : x j ⟨i, hj⟩ = v i := by
              subst j
              rfl
            exact ((hc _).1 i h rfl (hagree i h).symm).trans (transport _ _)
        · funext ⟨k, hk⟩
          subst j
          fin_cases k
          · exact hleft
          · exact hright
      · simp [hcoeff, hw]
    · simp [hc]
  · simp

/-- The same wire transports the index in either direction. -/
theorem move_restricts_with_wire_reverse (T : Raw I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) :
    (T.group p).Restricts ((T.group q).mul ((diagonal (Fin 2) K (T.Leg i₀)).group
      ![p i₀, q i₀])) := by
  apply restrict_trans (move_restricts_with_wire T q p i₀ (fun i hi => (hagree i hi).symm))
  exact mul_restricts (restrict_refl _) (grouped_wire_symm K (T.Leg i₀) _ _).1

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
