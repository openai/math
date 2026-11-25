import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import Mathlib.Analysis.Complex.Basic
import OAI.Combinatorics.Sunflower.Tensor

/-! The single-target convex-hull copying construction. A shared binary string indexed
by the alphabet supplies a sign at each possible label. Deleting the control position
at each source leaves a shared string just one bit shorter. -/

noncomputable section
open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Copy

abbrev Bits (n : ℕ) := Fin n → Bool

private def sign (b : Bool) : ℂ := if b then -1 else 1

private theorem sign_average {n : ℕ} (i j : Fin (n + 1)) (v : Bits n) :
    (∑ b : Bool, sign b / 2 * sign ((i.insertNth (α := fun _ ↦ Bool) b v) j)) =
      if i = j then 1 else 0 := by
  cases j using i.succAboveCases with
  | x => norm_num [Fintype.sum_bool, sign]
  | p j =>
    simp only [Fin.insertNth_apply_succAbove, Fin.ne_succAbove, ite_false, Fintype.sum_bool]
    cases v j <;> norm_num [sign]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Input and returned resource for copying one label to site `z` from the sources `P`. -/
abbrev input (P : Finset I) (z : I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ (insert z P) (Bits (n + 1))

abbrev returned (P : Finset I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ P (Bits n)

/-- Each local matrix reads its own control. At the target `z`, the control is the
desired output index of the copied vector, or the symbol to compare against. -/
def matrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n + 1))
    (x : (returned P n).Leg s) (y : (input P z n).Leg s) : ℂ :=
  let t : Bits (n+1) := if h : s ∈ insert z P then y h else fun _ ↦ false
  (if (∀ h : s ∈ P, x h = label.removeNth t) then 1 else 0) *
    (if s = s₀ then sign (t label) / 2 else 1) *
    (if s = z then sign (t label) else 1)

private theorem basis_product {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P)
    {n : ℕ} (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) (t : Bits (n+1)) :
    (∏ s, matrix P z s₀ n s (control s) (x s) (fun _ ↦ t)) =
      (if x = (fun _ _ ↦ i.removeNth t) then 1 else 0) *
      (sign (t i) / 2) * sign (t (control z)) := by
  classical
  have hlocal (s : I) :
      matrix P z s₀ n s (control s) (x s) (fun _ ↦ t) =
        (if (∀ h : s ∈ P, x s h = i.removeNth t) then 1 else 0) *
        (if s = s₀ then sign (t i) / 2 else 1) *
        (if s = z then sign (t (control z)) else 1) := by
    by_cases h : s ∈ P
    · have hi := hc s h
      have h' : s ∈ insert z P := Finset.mem_insert_of_mem h
      by_cases hz : s = z
      · subst s; simp [matrix, hi, h']
      · simp [matrix, hi, h', hz]
    · have hne : s ≠ s₀ := fun he ↦ h (he ▸ h₀)
      by_cases hz : s = z
      · subst s; simp [matrix, h, hne]
      · simp [matrix, h, hne, hz]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_boole]
  have hh : (∀ s (h : s ∈ P), x s h = i.removeNth t) ↔ x = (fun _ _ ↦ i.removeNth t) :=
    ⟨fun H ↦ funext fun s ↦ funext fun h ↦ H s h, fun H ↦ by rw [H]; simp⟩
  simp [hh]

private theorem sum_delete {n : ℕ} (i j : Fin (n+1)) (u : Bits n → ℂ) :
    (∑ t : Bits (n+1), u (i.removeNth t) * (sign (t i) / 2) * sign (t j)) =
      (if i = j then 1 else 0) * ∑ v, u v := by
  classical
  let term (t : Bits (n+1)) := u (i.removeNth t) * (sign (t i) / 2) * sign (t j)
  let e := Fin.insertNthEquiv (fun _ : Fin (n+1) ↦ Bool) i
  calc
    _ = ∑ bv : Bool × Bits n, term (e bv) := (e.sum_comp term).symm
    _ = ∑ v : Bits n, ∑ b : Bool, term (e (b,v)) :=
      (Fintype.sum_prod_type _).trans Finset.sum_comm
    _ = ∑ v : Bits n, u v * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      calc
        _ = ∑ b : Bool, u v * (sign b / 2 * sign ((i.insertNth (α := fun _ ↦ Bool) b v) j)) := by
          apply Finset.sum_congr rfl
          intro b _
          change u (i.removeNth (i.insertNth (α := fun _ ↦ Bool) b v)) *
            (sign ((i.insertNth (α := fun _ ↦ Bool) b v) i) / 2) * _ = _
          simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same, mul_assoc]
          rfl
        _ = _ := by rw [← Finset.mul_sum, sign_average]
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

private theorem deleted_sum {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) {n : ℕ}
    (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) :
    (∑ t : Bits (n+1), ∏ s, matrix P z s₀ n s (control s) (x s) (fun _ ↦ t)) =
      (if i = control z then 1 else 0) * (returned P n).coeff x := by
  classical
  calc
    _ = ∑ t : Bits (n+1), (if x = (fun _ _ ↦ i.removeNth t) then 1 else 0) *
        (sign (t i) / 2) * sign (t (control z)) :=
      Finset.sum_congr rfl (fun t _ ↦ basis_product h₀ control i hc x t)
    _ = _ := by
      simp only [returned, Raw.maskDiagonal, Crossing.basisTensor]
      convert sum_delete i (control z)
        (fun v ↦ if x = (fun (s : I) (_ : s ∈ P) ↦ v) then 1 else 0) using 1
      all_goals congr 1
      apply Finset.sum_congr
      · ext t
        simp
      · intro t _
        split_ifs with h₁ h₂ h₂
        · rfl
        · exact (h₂ (h₁.trans (by funext s h; rfl))).elim
        · exact (h₁ (h₂.trans (by funext s h; rfl))).elim
        · rfl

/-- The coefficient identity for the controlled conversion. It gives a basis vector
at the target, tensored with the returned partial diagonal, on the common-source promise. -/
theorem matrix_apply {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) {n : ℕ}
    (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) :
    contract (fun s ↦ matrix P z s₀ n s (control s)) (input P z n).coeff x =
      (if i = control z then 1 else 0) * (returned P n).coeff x := by
  classical
  exact (contract_maskDiagonal (K := ℂ) (B := fun s ↦ (returned P n).Leg s)
    (insert z P) (Bits (n+1)) (fun s ↦ matrix P z s₀ n s (control s)) x).trans
      (deleted_sum h₀ control i hc x)

/-- A basis label at the target site, padded with scalar factors elsewhere. -/
def labelAt (z : I) {n : ℕ} (i : Fin (n+1)) : Raw.{0} I ℂ :=
  ⟨MaskLeg {z} (Fin (n+1)), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ if i = x z (Finset.mem_singleton_self z) then 1 else 0⟩

/-- The copying matrix emits the chosen label at the target. Unlike the test matrix,
its target row supplies the label being tested. -/
def copyMatrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n+1))
    (x : (returned P n).Leg s × MaskLeg {z} (Fin (n+1)) s) (y : (input P z n).Leg s) : ℂ :=
  matrix P z s₀ n s (if h : s = z then x.2 (Finset.mem_singleton.mpr h) else label) x.1 y

/-- On the common-source promise the same local matrices for every `i` copy
the source label as an output basis vector and return the fixed resource. -/
theorem copyMatrix_apply {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) (hz : z ∉ P)
    {n : ℕ} (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s × MaskLeg {z} (Fin (n+1)) s) :
    contract (fun s ↦ copyMatrix P z s₀ n s (control s)) (input P z n).coeff x =
      ((returned P n).mul (labelAt z i)).coeff x := by
  let u (s : I) := if h : s = z then (x s).2 (Finset.mem_singleton.mpr h) else control s
  have hu (s : I) (hs : s ∈ P) : u s = i := by
    have hsz : s ≠ z := fun e ↦ hz (e ▸ hs)
    simp [u, hsz, hc s hs]
  calc
    _ = contract (fun s ↦ matrix P z s₀ n s (u s)) (input P z n).coeff
      (fun s ↦ (x s).1) := rfl
    _ = _ := by
      rw [matrix_apply h₀ u i hu]
      change (if i = u z then 1 else 0) * _ =
        _ * (if i = (x z).2 (Finset.mem_singleton_self z) then 1 else 0)
      rw [mul_comm]
      simp [u]

variable [Nonempty I]

private theorem price_bits (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (c : ℝ) {P : Finset I} (hP : P.Nonempty) (n : ℕ) :
    rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin n → Bool)) = maskDiagonalPrice φ c P * n := by
  classical
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  let e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard
  have hp : rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin n → Bool)) =
      rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin (2 ^ n))) :=
    congrArg (fun x ↦ c * Real.logb 2 (φ.val x : ℝ)) (ofRaw_maskDiagonal_equiv P hP e)
  rw [hp, rawLogPrice_maskDiagonal φ c P hP (by positivity)]
  simp [Real.logb_pow]

/-- When adjoining the target preserves the diagonal price, testing an alphabet
of any size costs exactly the price of one extra source bit. -/
theorem cost_eq {P : Finset I} {z : I}
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (hP : P.Nonempty)
    (c : ℝ) (h : maskDiagonalPrice φ c (insert z P) = maskDiagonalPrice φ c P) (n : ℕ) :
    rawLogPrice φ c (input P z n) - rawLogPrice φ c (returned P n) = maskDiagonalPrice φ c P := by
  unfold input returned
  rw [price_bits φ c (Finset.insert_nonempty z P), price_bits φ c hP, h]
  push_cast
  ring

end Copy
end Sunflower
end Combinatorics
end OAI
