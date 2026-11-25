import OAI.LinearAlgebra.SpectralBooks.BooleanSort

namespace OAI
/-! # Simultaneous multiset equality for bounded words

Two lists of the same arbitrary length are padded with equal numbers of zero records and
sorted by Batcher networks. Comparing the two sorted bit strings tests equality including
multiplicity. The padding proof permits zeros in the input.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

open ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork ExactQuantumFactoring.BitArithmetic

private def paddedWords {m w : ℕ} (x : Fin m → Fin (2^w)) : Wires (Nat.clog 2 m) (Fin (2^w)) :=
  fun i ↦ if h : i.val < m then x ⟨i.val, h⟩ else 0

private theorem ofFn_paddedWords {m w : ℕ} (x : Fin m → Fin (2^w)) :
    List.ofFn (paddedWords x) =
      List.ofFn x ++ List.replicate (2^(Nat.clog 2 m) - m) 0 := by
  let extra := 2^(Nat.clog 2 m) - m
  have hlen : m + extra = 2^(Nat.clog 2 m) := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) m
    dsimp [extra]
    omega
  have he : (fun j : Fin (m+extra) ↦ paddedWords x (j.cast hlen)) =
      Fin.append x (fun _ : Fin extra ↦ 0) := by
    funext j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp [paddedWords]
    · simp [paddedWords]
  rw [List.ofFn_congr hlen.symm, he, List.ofFn_fin_append, List.ofFn_const]

/-- Pad a raw table to the next power of two. Every additional bit is zero. -/
private def padWords (m w : ℕ) : BooleanNetwork (m*w) (2^(Nat.clog 2 m)*w) :=
  vector (fun b ↦
    let p := finProdFinEquiv.symm b
    if h : p.1.val < m then bit (finProdFinEquiv (⟨p.1.val, h⟩, p.2)) else constant false)

private theorem padWords_eval {m w : ℕ} (x : Fin m → Fin (2^w)) :
    (padWords m w).eval (encodeWords x) = encodeWords (paddedWords x) := by
  funext b
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective b
  simp only [padWords, eval_vector, Equiv.symm_apply_apply, encodeWords_at, paddedWords]
  split
  · rw [eval_bit, encodeWords_at]
  · simp [wordBits]

private theorem padWords_count (m w : ℕ) : (padWords m w).net.count ≤ 2^(Nat.clog 2 m)*w := by
  have h : ∀ i : Fin (2^(Nat.clog 2 m)*w),
      (if h : (finProdFinEquiv.symm i).1.val < m then
        bit (finProdFinEquiv (⟨(finProdFinEquiv.symm i).1.val, h⟩, (finProdFinEquiv.symm i).2))
       else constant false : BooleanNetwork (m*w) 1).net.count ≤ 1 := by
    intro i
    by_cases hi : (finProdFinEquiv (m := 2^Nat.clog 2 m) (n := w)).symm i |>.1.val < m
    · exact le_trans (le_of_eq (congrArg (fun c : BooleanNetwork (m*w) 1 ↦ c.net.count)
        (dite_eq_left hi))) (by simp)
    · exact le_trans (le_of_eq (congrArg (fun c : BooleanNetwork (m*w) 1 ↦ c.net.count)
        (dite_eq_right hi))) (by simp)
  simpa [padWords] using count_vector_le _ h

private def paddedSort (m w : ℕ) : BooleanNetwork (m*w) (2^(Nat.clog 2 m)*w) :=
  (padWords m w).comp (booleanSort (Nat.clog 2 m) w)

private theorem paddedSort_eval {m w : ℕ} (x : Fin m → Fin (2^w)) :
    (paddedSort m w).eval (encodeWords x) =
      encodeWords ((sortNet (Nat.clog 2 m)).eval (paddedWords x)) := by
  rw [paddedSort, BooleanNetwork.eval_comp, padWords_eval, booleanSort_eval]

theorem sortNet_eq_iff_perm {k : ℕ} {α : Type*} [LinearOrder α] (x y : Wires k α) :
    (sortNet k).eval x = (sortNet k).eval y ↔ (List.ofFn x).Perm (List.ofFn y) := by
  have hx := (sortNet k).perm_ofFn_eval x
  have hy := (sortNet k).perm_ofFn_eval y
  constructor
  · intro h
    rw [h] at hx
    exact hx.symm.trans hy
  · intro h
    exact List.ofFn_injective ((hx.trans (h.trans hy.symm)).eq_of_sortedLE
      (sortNet_monotone x).sortedLE_ofFn (sortNet_monotone y).sortedLE_ofFn)

/-- Canonical-order equality on two consecutive tables of `m` unsigned `w`-bit records. -/
def multisetEq (m w : ℕ) : BooleanNetwork (m*w + m*w) 1 :=
  if m = 0 then constant true else
    let a := (select (Fin.castAdd (m*w))).comp (paddedSort m w)
    let b := (select (Fin.natAdd (m*w))).comp (paddedSort m w)
    (a.pair b).comp (wordEq (2^(Nat.clog 2 m)*w))

/-- The one output bit tests equality of record multiplicities on the unpadded lists. -/
theorem multisetEq_eval {m w : ℕ} (x y : Fin m → Fin (2^w)) :
    (multisetEq m w).eval (Fin.append (encodeWords x) (encodeWords y)) 0 = true ↔
      (List.ofFn x).Perm (List.ofFn y) := by
  by_cases hm : m = 0
  · subst m
    simp [multisetEq]
  simp only [multisetEq, hm, ite_false, BooleanNetwork.eval_comp, eval_pair, eval_select]
  have h₁ : Fin.append (encodeWords x) (encodeWords y) ∘ Fin.castAdd (m*w) = encodeWords x :=
    funext (Fin.append_left _ _)
  have h₂ : Fin.append (encodeWords x) (encodeWords y) ∘ Fin.natAdd (m*w) = encodeWords y :=
    funext (Fin.append_right _ _)
  rw [h₁, h₂, paddedSort_eval, paddedSort_eval, wordEq_eval, decide_eq_true_eq]
  have hb {q : ℕ} (a b : Basis q) : bitsValue a = bitsValue b ↔ a = b := (bitsEquiv q).injective.eq_iff
  have hw {r : ℕ} (a b : Fin r → Fin (2^w)) : encodeWords a = encodeWords b ↔ a = b :=
    (Function.LeftInverse.injective (decodeWords_encodeWords (r := r) (w := w))).eq_iff
  rw [hb, hw, sortNet_eq_iff_perm, ofFn_paddedWords, ofFn_paddedWords, List.perm_append_right_iff]

private theorem pow_clog_le_twice {m : ℕ} (hm : 0 < m) : 2^(Nat.clog 2 m) ≤ 2*m := by
  cases h : Nat.clog 2 m with
  | zero => simp; omega
  | succ k =>
    have ht := Nat.pow_lt_of_lt_clog (b := 2) (x := m) (show k < Nat.clog 2 m by omega)
    rw [pow_succ]
    omega

/-- An explicit quasilinear bound at arbitrary list lengths, including the empty batch. -/
theorem multisetEq_count (m w : ℕ) :
    (multisetEq m w).net.count ≤ 1 + 700*m*(Nat.clog 2 m+1)^2*(w+1) := by
  by_cases hm : m = 0
  · subst m
    simp [multisetEq]
  let k := Nat.clog 2 m
  have hp : 2^k ≤ 2*m := pow_clog_le_twice (Nat.pos_of_ne_zero hm)
  have hrows : 2^k ≤ 2*m*(k+1)^2 := Nat.le_trans hp (Nat.le_mul_of_pos_right _ (by positivity))
  have hc : 2^k*k*(k+1)/4 ≤ 2*m*(k+1)^2 := by
    calc
      _ ≤ 2^k*k*(k+1) := Nat.div_le_self _ _
      _ ≤ 2*m*(k+1)*(k+1) := by gcongr; omega
      _ = _ := by ring
  have hpad := padWords_count m w
  have hsort := booleanSort_count k w
  have heq := wordEq_count (2^k*w)
  change (padWords m w).net.count ≤ 2^k*w at hpad
  have hb := Nat.mul_le_mul_right w hrows
  have hs := Nat.mul_le_mul_right (110*w+18) hc
  rw [multisetEq, ite_eq_right hm]
  simp only [count_comp, count_pair, count_select, paddedSort, zero_add]
  change ((padWords m w).net.count + (booleanSort k w).net.count) +
    ((padWords m w).net.count + (booleanSort k w).net.count) + (wordEq (2^k*w)).net.count ≤ _
  have hcost := Nat.mul_le_mul_left 96 hb
  have hone : 1 ≤ m*(k+1)^2 := Nat.mul_pos (Nat.pos_of_ne_zero hm) (by positivity)
  nlinarith only [hpad, hsort, heq, hb, hs, hcost, hone, Nat.zero_le (m*(k+1)^2*w)]

/-- Test two arbitrary tables already computed on the same input, evaluating each source once. -/
def multisetEqOn {n m w : ℕ} (a b : BooleanNetwork n (m*w)) : BooleanNetwork n 1 :=
  (a.pair b).comp (multisetEq m w)

theorem multisetEqOn_eval {n m w : ℕ} (a b : BooleanNetwork n (m*w)) (z : Basis n) :
    (multisetEqOn a b).eval z 0 = true ↔
      (List.ofFn (decodeWords (a.eval z))).Perm (List.ofFn (decodeWords (b.eval z))) := by
  simpa [multisetEqOn, BooleanNetwork.eval_comp, eval_pair] using
    multisetEq_eval (decodeWords (a.eval z)) (decodeWords (b.eval z))

theorem multisetEqOn_count {n m w : ℕ} (a b : BooleanNetwork n (m*w)) :
    (multisetEqOn a b).net.count ≤ a.net.count+b.net.count+1+700*m*(Nat.clog 2 m+1)^2*(w+1) := by
  rw [multisetEqOn, count_comp, count_pair]
  have := multisetEq_count m w
  omega

end LinearAlgebra.SpectralBooks.Batcher

end OAI
