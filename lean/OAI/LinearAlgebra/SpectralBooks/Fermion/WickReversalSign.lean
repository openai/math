import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversal

/-! # Signs of Wick contractions under exchange of the blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

variable {α k : Type*} [CommRing k]

/-- The number of contracted pairs. -/
def edges : {l r : List α} → Matching l r → ℕ
  | [], _, _ => 0
  | _ :: _, _, .inl p => edges p
  | _ :: _, _, .inr ⟨_,p⟩ => edges p + 1

theorem edges_le {l r : List α} (p : Matching l r) : edges p ≤ l.length ∧ edges p ≤ r.length := by
  induction l generalizing r with
  | nil => simp [edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · have := ih p
      simp only [edges, List.length_cons]
      omega
    · have h := ih p
      rw [List.length_eraseIdx_of_lt j.isLt] at h
      have := j.isLt
      simp only [edges, List.length_cons]
      omega

@[simp] theorem edges_skipCol (x : α) {l r : List α} (p : Matching l r) :
    edges (skipCol x p) = edges p := by
  induction l generalizing r with
  | nil => rfl
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [skipCol, edges, ih]

@[simp] theorem edges_pairAt (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) : edges (pairAt x j p) = edges p + 1 := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · rfl
    · change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩ <;> simp [pairAt, edges, ih]

@[simp] theorem edges_noCols (l : List α) : edges (noCols l) = 0 := by
  induction l <;> simp [noCols, edges, *]

@[simp] theorem edges_reverse {l r : List α} (p : Matching l r) : edges (reverse p) = edges p := by
  induction l generalizing r with
  | nil => simp [reverse, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [reverse, edges, ih]

theorem weight_skipCol (κ : α → α → k) (x : α) {l r : List α} (p : Matching l r) :
    weight κ (skipCol x p) = (-1 : k) ^ edges p * weight κ p := by
  induction l generalizing r with
  | nil => simp [weight, edges]
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩
    · simp [skipCol, weight, edges, ih]
    · simp only [skipCol, weight, edges, Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ, ih, pow_succ]
      ring

theorem weight_pairAt (κ : α → α → k) (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    weight κ (pairAt x j p) = (-1 : k) ^ (l.length - (j.val + 1)) * κ l[j.val] x * weight κ p := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · simp [pairAt, weight]
    · change Matching (y :: l.eraseIdx j) r at p
      have hlt : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hlen : l.length = (l.eraseIdx j).length + 1 := by rw [List.length_eraseIdx_of_lt hlt]; omega
      rcases p with p | ⟨t,p⟩
      · simp [pairAt, weight, ih]
      · simp only [pairAt, weight, Fin.val_succ, List.getElem_cons_succ, List.length_cons,
          Nat.add_sub_add_right, List.eraseIdx_cons_succ, ih, pow_succ]
        rw [show (-1 : k)^l.length = (-1)^(l.eraseIdx j).length * (-1) by rw [hlen, pow_succ]]
        ring

@[simp] theorem weight_noCols (κ : α → α → k) (l : List α) : weight κ (noCols l) = 1 := by
  induction l <;> simp [noCols, weight, *]

private theorem sign_skip {l r q : ℕ} (hl : q ≤ l) (hr : q ≤ r) :
    (-1 : k)^q * (-1)^(l*r + (l-q)*(r-q)) =
      (-1)^((l+1)*r + (l+1-q)*(r-q)) := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (R := k) ((l+1)*r + _)]
  congr 1
  rw [show l+1-q = (l-q)+1 by omega, Nat.add_mul, Nat.add_mul]
  simp only [one_mul]
  omega

private theorem sign_pair {l r q j : ℕ} (hj : j ≤ r) :
    ((-1 : k)^(r-j) * (-1)) * (-1)^(l*r + (l-q)*(r-q)) =
      (-1)^((l+1)*(r+1) + (l-q)*(r-q)) * ((-1)^l * (-1)^j) := by
  rw [← pow_succ, ← pow_add, ← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (R := k) ((l+1)*(r+1) + (l-q)*(r-q) + _)]
  congr 1
  simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
  omega

/-- In the reversed term each edge has been reoriented. With a minus sign
on that reversed kernel, the remaining sign is the product of the original
block-exchange sign and the sign exchanging the two blocks of unpaired fields. -/
theorem weight_reverse (κ : α → α → k) {l r : List α} (p : Matching l r) :
    weight (fun x y ↦ -κ y x) (reverse p) =
      (-1 : k)^(l.length*r.length + (l.length-edges p)*(r.length-edges p)) * weight κ p := by
  induction l generalizing r with
  | nil => simp [reverse, weight, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, weight_skipCol, edges_reverse, ih, edges, weight, List.length_cons,
        ← mul_assoc, sign_skip (edges_le p).1 (edges_le p).2]
    · simp only [reverse, weight_pairAt, ih, edges, weight, List.length_cons]
      let t := (r.eraseIdx j.val).length
      have ht : r.length = t + 1 := by
        dsimp [t]
        rw [List.length_eraseIdx_of_lt j.isLt]
        have := j.isLt
        omega
      have hj : j.val ≤ t := by have := j.isLt; omega
      have he := sign_pair (k := k) (l := l.length) (q := edges p) hj
      have hr : r.length - (j.val+1) = t-j.val := by omega
      have hb : r.length - (edges p+1) = t-edges p := by omega
      rw [hr, hb, Nat.add_sub_add_right]
      rw [show (l.length+1)*r.length = (l.length+1)*(t+1) by rw [ht]]
      change (-1 : k) ^ (t-↑j) * -κ x r[↑j] *
          ((-1) ^ (l.length*t + (l.length-edges p)*(t-edges p)) * weight κ p) = _
      linear_combination he * κ x r[↑j] * weight κ p

end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
