import OAI.LinearAlgebra.FiniteFourier.FourierSectors
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Synchronizing local words over a coefficient ring

Each slot applies an arbitrary scaled permutation followed by either the
identity or a Fourier stage. Zero scalings are allowed so a singular diagonal
from elimination fits into the same word.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {I : Type} [Fintype I] [DecidableEq I]

/-- An output permutation with independent, possibly zero, scalings. -/
def kernelMonomial (e : Equiv.Perm I) (c : I → R) : Matrix I I R :=
  fun i j => if e i = j then c i else 0

omit [Fintype I] in
private theorem kernelMonomial_one :
    kernelMonomial (Equiv.refl I) (fun _ => (1 : R)) = 1 := rfl

/-- Synchronized local word with a fixed number of monomial and Fourier slot pairs. -/
def KernelWord (p : ℕ) (ζ : R) : ℕ → Matrix I I R → Prop
  | 0, A => A = 1
  | n+1, A => ∃ (e : Equiv.Perm I) (c : I → R) (F P : Matrix I I R),
      (F = 1 ∨ Nonempty (PrimeFourierSectors p ζ F)) ∧ KernelWord p ζ n P ∧
      A = F * kernelMonomial e c * P

namespace KernelWord

theorem identity (p : ℕ) (ζ : R) (I : Type) [Fintype I] [DecidableEq I] :
    KernelWord p ζ 0 (1 : Matrix I I R) := rfl

theorem monomial (p : ℕ) (ζ : R) (e : Equiv.Perm I) (c : I → R) :
    KernelWord p ζ 1 (fun i j => if e i = j then c i else 0) :=
  ⟨e, c, 1, 1, Or.inl rfl, rfl, by simp only [one_mul, mul_one]; rfl⟩

theorem fourier {p : ℕ} {ζ : R} {A : Matrix I I R} (h : PrimeFourierSectors p ζ A) :
    KernelWord p ζ 1 A :=
  ⟨Equiv.refl _, fun _ => 1, A, 1, Or.inr ⟨h⟩, rfl, by simp [kernelMonomial_one]⟩

theorem diagonal (p : ℕ) (ζ : R) (c : I → R) : KernelWord p ζ 1 (Matrix.diagonal c) := by
  exact monomial p ζ (Equiv.refl _) c

theorem mul {p m n : ℕ} {ζ : R} {A B : Matrix I I R}
    (hA : KernelWord p ζ m A) (hB : KernelWord p ζ n B) :
    KernelWord p ζ (m+n) (A*B) := by
  induction m generalizing A with
  | zero => obtain rfl : A = 1 := hA; simpa using hB
  | succ m ih =>
    obtain ⟨e, c, F, P, hF, hP, rfl⟩ := hA
    rw [Nat.succ_add]
    exact ⟨e, c, F, P*B, hF, ih hP, Matrix.mul_assoc ..⟩

theorem pad {p m n : ℕ} {ζ : R} {A : Matrix I I R}
    (hA : KernelWord p ζ m A) (hle : m ≤ n) : KernelWord p ζ n A := by
  induction n, hle using Nat.le_induction with
  | base => exact hA
  | succ n _ ih =>
    exact ⟨Equiv.refl _, fun _ => 1, 1, A, Or.inl rfl, ih, by simp [kernelMonomial_one]⟩

private theorem listTransvections {p t : ℕ} {ζ : R} (L : List (Matrix.TransvectionStruct I R))
    (h : ∀ T ∈ L, KernelWord p ζ t T.toMatrix) :
    KernelWord p ζ (t * L.length) (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp; exact KernelWord.identity p ζ I
  | cons a L ih =>
    simp only [List.length_cons, Nat.mul_succ, List.map_cons, List.prod_cons]
    rw [Nat.add_comm]
    exact (h a (by simp)).mul (ih fun T hT => h T (by simp [hT]))

/-- Compiling a diagonal factorization costs one slot plus the total number
of transvections times their common word length. -/
theorem of_factorization {p t b : ℕ} {ζ : R} {A : Matrix I I R}
    (L L' : List (Matrix.TransvectionStruct I R)) (D : I → R)
    (hb : L.length + L'.length ≤ b)
    (hf : A = (L.map Matrix.TransvectionStruct.toMatrix).prod *
      Matrix.diagonal D * (L'.map Matrix.TransvectionStruct.toMatrix).prod)
    (hL : ∀ T ∈ L, KernelWord p ζ t T.toMatrix)
    (hL' : ∀ T ∈ L', KernelWord p ζ t T.toMatrix) : KernelWord p ζ (t * b + 1) A := by
  rw [hf]
  apply (((listTransvections L hL).mul (diagonal p ζ D)).mul (listTransvections L' hL')).pad
  have := Nat.mul_le_mul_left t hb
  rw [Nat.mul_add] at this
  omega

end KernelWord

end FiniteFourier
end LinearAlgebra
end OAI
