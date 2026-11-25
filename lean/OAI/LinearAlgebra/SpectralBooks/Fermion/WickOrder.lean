import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFields

/-! # Partial matchings in the product of two normal-ordered fermion words

A matching either retains the first field of the left word, or pairs it with
one remaining field of the right word and erases that field. The matched
scalar is central, and its sign counts the intervening fields.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open scoped BigOperators

variable {α : Type*}

/-- Partial bipartite matchings of the positions of two words. -/
def Matching : List α → List α → Type
  | [], _ => Unit
  | _ :: l, r => Matching l r ⊕ Σ j : Fin r.length, Matching l (r.eraseIdx j.val)

instance matchingFintype : (l r : List α) → Fintype (Matching l r)
  | [], _ => inferInstanceAs (Fintype Unit)
  | _ :: l, r => by
    letI := matchingFintype l r
    letI (j : Fin r.length) := matchingFintype l (r.eraseIdx j.val)
    exact inferInstanceAs (Fintype (_ ⊕ Σ _ : Fin r.length, _))

namespace Matching

/-- All unmatched fields, in their original order across both blocks. -/
def residual : {l r : List α} → Matching l r → List α
  | [], r, _ => r
  | x :: _, _, .inl m => x :: residual m
  | _ :: _, _, .inr ⟨_, m⟩ => residual m

/-- The product of all scalar kernels, with the sign from bringing each matched
pair together in the order first-field then second-field. -/
def weight {k : Type*} [CommRing k] (κ : α → α → k) :
    {l r : List α} → Matching l r → k
  | [], _, _ => 1
  | _ :: _, _, .inl m => weight κ m
  | x :: l, r, .inr ⟨j, m⟩ =>
    ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) * weight κ m

/-- Erasing the two fields of a pair preserves the parity of the total length. -/
theorem residual_sign {k : Type*} [CommRing k] (l r : List α) (p : Matching l r) :
    (-1 : k) ^ (residual p).length = (-1 : k) ^ l.length * (-1 : k) ^ r.length := by
  induction l generalizing r with
  | nil => simp [residual]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simpa [residual, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun v : k ↦ v * (-1)) (ih r p)
    · rw [residual, ih]
      have h := j.isLt
      have hlen : (r.eraseIdx j.val).length + 1 = r.length := by
        rw [List.length_eraseIdx_of_lt h]
        omega
      rw [List.length_cons, ← congrArg (fun n : ℕ ↦ (-1 : k) ^ n) hlen, pow_succ, pow_succ]
      ring

end Matching

variable {k E : Type*} [CommRing k] [Ring E] [Algebra k E]

/-- Evaluate each signed matching on an arbitrary function of its residual word. -/
def wickSum (κ : α → α → k) (H : List α → E) (l r : List α) : E :=
  ∑ p : Matching l r, p.weight κ • H p.residual

private theorem wickSum_cons (κ : α → α → k) (H : List α → E) (x : α) (l r : List α) :
    wickSum κ H (x :: l) r = wickSum κ (fun w ↦ H (x :: w)) l r +
      ∑ j : Fin r.length, ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) •
        wickSum κ H l (r.eraseIdx j.val) := by
  unfold wickSum
  change (∑ p : Matching l r ⊕ (Σ j : Fin r.length, Matching l (r.eraseIdx j.val)), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Matching.residual, Matching.weight, Finset.smul_sum, smul_smul]

variable (C A : α → E) (κ : α → α → k)

private theorem wickSum_normal_cons (x : α) (l r : List α) :
    wickSum κ (fun w ↦ normal k C A (x :: w)) l r =
      C x * wickSum κ (normal k C A) l r + ((-1 : k)^l.length * (-1 : k)^r.length) •
        (wickSum κ (normal k C A) l r * A x) := by
  simp only [wickSum, normal, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Matching.residual_sign, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul,
    mul_comm (m.weight κ) _]

/-- The finite Wick expansion for two normal products. Each partial matching
contracts only pairs between the two blocks, and the remaining fields stay
inside a single normal product in their original order. -/
theorem normal_mul_normal
    (hac : ∀ x y, A x * C y + C y * A x = algebraMap k E (κ x y))
    (haa : ∀ x y, A x * A y + A y * A x = 0) (l r : List α) :
    normal k C A l * normal k C A r =
      ∑ p : Matching l r, p.weight κ • normal k C A p.residual := by
  change _ = wickSum κ (normal k C A) l r
  induction l generalizing r with
  | nil =>
    change (1 : E) * normal k C A r = ∑ _ : Unit, (1 : k) • normal k C A r
    simp
  | cons x l ih =>
    rw [normal, wickSum_cons, wickSum_normal_cons, ← ih]
    simp_rw [← ih]
    rw [add_mul, smul_mul_assoc, mul_assoc, mul_assoc, ann_mul_normal C A κ hac haa, mul_add,
      smul_add, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul, mul_assoc, add_assoc]
    simp only [mul_smul_comm, smul_smul]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
