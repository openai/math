import OAI.LinearAlgebra.MatrixExponent.Spectral.CubeGadget
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path

/-!
# Exact six-site and cube packets

The selector set is independent of the common bundle width `z`. Within
a summand, a permitted pair receives a whole number of width-`z` bundles.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable (K : Type) [Field K]

private theorem expand_profile {S I J : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype I] [Fintype J] (A : I → S × S) (hA : ∀ i, (A i).1 ≠ (A i).2)
    (B : J → S × S) (w C : ℕ) (H : Finset (J → ℕ)) (z : ℕ)
    (h : (∏ i, wire K (A i).1 (A i).2 2) ^ w ≤
      (C : Tensor K S) * ∑ q ∈ H, ∏ j, wire K (B j).1 (B j).2 2 ^ (q j * z)) :
    Packet K (fun e : I × Fin w => A e.1)
      (fun i : Fin C × ↥H => fun e : Σ j : J, Fin (i.2.1 j * z) => B e.1) := by
  classical
  apply packet_of_restriction _ (fun e => hA e.1)
  simp only [Fintype.prod_prod_type, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow, Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_coe_sort H (fun q => ∏ j, wire K (B j).1 (B j).2 2 ^ (q j * z))]
  exact h

def sixDemandPair : Fin 2 → Fin 6 × Fin 6 := ![(0, 1), (2, 3)]

theorem six_packets :
    ∃ (b C : ℕ) (H : Finset (Fin 8 → ℕ)), 0 < b ∧
      (∀ h ∈ H, ∑ i, h i < 4 * b) ∧ ∀ z : ℕ, 0 < z →
        Packet K (fun e : Fin 2 × Fin (b * z) => sixDemandPair e.1)
          (fun i : Fin C × ↥H => fun e : Σ j : Fin 8, Fin (i.2.1 j * z) => sixPair e.1) := by
  obtain ⟨b, C, H, hb, hcost, h⟩ := six_site K
  refine ⟨b, C, H, hb, hcost, fun z hz => ?_⟩
  apply expand_profile K sixDemandPair (by decide) sixPair
  rw [Fin.prod_univ_two]
  exact h z hz

theorem cube_packets (L k₀ : ℕ) (hL : 0 < L) :
    ∃ n ≥ k₀, ∃ (b C : ℕ) (H : Finset (Cube n × Fin n → ℕ)), 0 < b ∧
      (∀ h ∈ H, L * ∑ i, h i < n * Fintype.card (Cube n) * b) ∧ ∀ z : ℕ, 0 < z →
        Packet K (fun e : Cube n × Fin (b * z) => (e.1, Cube.flip Finset.univ e.1))
          (fun i : Fin C × ↥H => fun e : Σ j : Cube n × Fin n, Fin (i.2.1 j * z) =>
            (e.1.1, Cube.flip {e.1.2} e.1.1)) := by
  obtain ⟨n, hn, b, C, H, hb, hcost, h⟩ := cube_site K L (k₀ + 1) hL
  refine ⟨n, by omega, b, C, H, hb, hcost, fun z hz => ?_⟩
  have ha (x : Cube n) : x ≠ Cube.flip Finset.univ x := by
    intro he
    have := congrFun he (⟨0, by omega⟩ : Fin n)
    simp [Cube.flip] at this
  refine expand_profile K (fun x : Cube n => (x, Cube.flip Finset.univ x)) ha
    (fun i : Cube n × Fin n => (i.1, Cube.flip {i.2} i.1)) (b * z) C H z ?_
  exact h z hz

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
