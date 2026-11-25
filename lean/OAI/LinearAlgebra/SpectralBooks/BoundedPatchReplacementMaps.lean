import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordStraightening
import OAI.LinearAlgebra.SpectralBooks.PortWiring
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchRootCost

/-! # Uniform straightening maps for a bounded patch

The field matrices in a straightening identity are chosen before the entries of the
patch are supplied. Transposing a matrix into a corner table preserves its physical
label. The entries after transposition are linear formulas in the original entries.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

section

open SiteTensor

/-- Apply given local matrices by transposition at the table pairing. -/
theorem tablePairing_transpose {V F R : Type*} [Fintype V] [CommSemiring F] [CommSemiring R]
    (h : F →+* R) {A B : V → Type*} [∀ v, Fintype (A v)] [∀ v, Fintype (B v)]
    (Y : (∀ v, B v) → F) (X : (∀ v, A v) → F) (M : ∀ v, B v → A v → F)
    (hM : ∀ x, Y x = ∑ a, X a * ∏ i, M i (x i) (a i)) (U : ∀ v, B v → R) :
    tablePairing h Y U = tablePairing h X (fun v a => ∑ b, h (M v b a) * U v b) := by
  simp only [tablePairing, hM, map_sum, map_mul, map_prod, Finset.sum_mul, Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem tablePairing_sum {V T F R : Type*} [Fintype V] [Fintype T] [CommSemiring F] [CommSemiring R]
    (h : F →+* R) {A : V → Type*} [∀ v, Fintype (A v)] (z : T → (∀ v, A v) → F)
    (U : ∀ v, A v → R) : tablePairing h (∑ t, z t) U = ∑ t, tablePairing h (z t) U := by
  simp only [tablePairing, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

namespace ChordGraph

/-- A common choice of maps for every specialization of the corner tables. The constant
in the term count is uniform over all polygon sizes up to `5*K`. -/
theorem bounded_patch_maps {F : Type*} [Field F]
    (noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    (K : ℕ) (hK : 0 < K) :
    ∃ c : ℕ, ∀ (n : ℕ), n+1 ≤ 5*K → ∀ (w : ℕ) (g : Widths (n+1)), total g ≤ 4*K*w →
      ∀ (R : Raw.{0} (Fin (n+1)) F), ofRaw R = graphClass F g →
      ∀ S : Widths (n+1) → Raw.{0} (Fin (n+1)) F, (∀ a, ofRaw (S a) = graphClass F a) →
      ∃ (L : ℕ) (t : Fin L → Widths (n+1))
        (M : ∀ j i, R.Leg i → (S (t j)).Leg i → F),
        L ≤ 2^(w+c) ∧ (∀ j, Noncrossing (t j) ∧ ∀ i, load i (t j) ≤ load i g) ∧
        ∀ x, R.coeff x = ∑ j, ∑ a, (S (t j)).coeff a * ∏ i, M j i (x i) (a i) := by
  let η := 1 / (4 * (K : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  choose C hC using fun n : ℕ => straighten_of_no_plane (k := n+1) noPlane hη
  let c := ∑ n ∈ Finset.range (5*K), C n
  refine ⟨c, fun n hn w g hg R hR S hS => ?_⟩
  obtain ⟨L,t,z,hL,hz,ht⟩ := hC n g R hR
  have hres (j : Fin L) : Crossing.IsRestriction (z j) (S (t j)).coeff := by
    apply (ofRaw_le_iff (X := {R with coeff := z j}) (Y := S (t j))).mp
    rw [hS]
    exact (ht j).2.2
  choose M hM using hres
  refine ⟨L,t,M,?_,fun j => ⟨(ht j).1,(ht j).2.1⟩,fun x => ?_⟩
  · have hC' : C n ≤ c := Finset.single_le_sum (f := C) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have hwidth : η * total g ≤ w := by
      dsimp only [η]
      rw [one_div, inv_mul_eq_div]
      apply (div_le_iff₀ (by positivity)).2
      have h : (total g : ℝ) ≤ 4 * (K : ℝ) * w := by exact_mod_cast hg
      linarith
    have bound := hL.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (add_le_add hwidth (by exact_mod_cast hC' : (C n : ℝ) ≤ c)))
    rw [← Nat.cast_add, Real.rpow_natCast] at bound
    exact_mod_cast bound
  · rw [hz, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact (hM j x).trans (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))

end ChordGraph

namespace PlanarPatch

open MvPolynomial

theorem HasFormula.fintypeSum {F I A : Type*} [Field F] [Fintype A] {C : ℕ}
    {p : A → MvPolynomial I F} (hC : 1 ≤ C) (hp : ∀ a, HasFormula C (p a)) :
    HasFormula ((Fintype.card A + 1) * C) (∑ a, p a) := by
  let e := (Fintype.equivFin A).symm
  rw [← e.sum_comp p]
  exact HasFormula.finSum hC (fun i => hp (e i))

namespace CornerTable

/-- Apply the transpose of a local restriction while retaining a corner's free leg. -/
def transpose {R A B V : Type*} [CommSemiring R] [Fintype A] {d : V → ℕ}
    (U : CornerTable R d A) (M : A → B → R) : CornerTable R d B :=
  match U with
  | .scalar u => .scalar (fun b => ∑ a, M a b * u a)
  | .stub v u => .stub v (fun b r => ∑ a, M a b * u a r)

@[simp] theorem label_transpose {R A B V : Type*} [CommSemiring R] [Fintype A] {d : V → ℕ}
    (U : CornerTable R d A) (M : A → B → R) : (U.transpose M).label = U.label := by
  cases U <;> rfl

@[simp] theorem value_transpose {R A B V : Type*} [CommSemiring R] [Fintype A] {d : V → ℕ}
    (U : CornerTable R d A) (M : A → B → R) (x : ∀ v, Fin (d v)) (b : B) :
    (U.transpose M).value x b = ∑ a, M a b * U.value x a := by
  cases U <;> rfl

theorem transpose_formulaBound {F I A B V : Type*} [Field F] [Fintype A] {d : V → ℕ}
    (U : CornerTable (MvPolynomial I F) d A) (M : A → B → F) {W : ℕ} (hU : U.FormulaBound W) :
    (U.transpose (fun a b => C (M a b))).FormulaBound ((Fintype.card A + 1) * (1 + W)) := by
  cases U with
  | scalar u => exact fun _ => HasFormula.fintypeSum (by omega) (fun a => (HasFormula.const _).mul (hU a))
  | stub v u => exact fun _ c => HasFormula.fintypeSum (by omega) (fun a => (HasFormula.const _).mul (hU a c))

end CornerTable
end PlanarPatch
end

end

end SpectralBooks
end LinearAlgebra
end OAI
