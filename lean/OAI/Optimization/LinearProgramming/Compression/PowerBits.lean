import OAI.Optimization.LinearProgramming.RAM.Basic
import OAI.Optimization.LinearProgramming.Compression.Proxy
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Sizes of the rational products used to evaluate an affine form in minor logarithms. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

private theorem log2_le_of_le_mul {z x y : ℕ} (h : z ≤ x * y) :
    z.log2 ≤ x.log2 + y.log2 + 1 := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  apply Nat.le_of_lt_succ
  apply (Nat.log2_lt hz.ne').2
  calc
    z ≤ x * y := h
    _ < 2^(x.log2 + 1) * 2^(y.log2 + 1) :=
      (Nat.mul_le_mul_right y (Nat.lt_log2_self (n := x)).le).trans_lt
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_log2_self (n := y)) (by positivity))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Reduced numerator and denominator separately divide the unreduced product.
The encoding length of a product is at most the sum of its input lengths. -/
theorem ratBits_mul_le_add (q r : ℚ) : ratBits (q * r) ≤ ratBits q + ratBits r := by
  have hn : (q*r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
    rw [Rat.mul_num, ← Int.natAbs_mul]
    apply Int.natAbs_ediv_le_natAbs
  have hd : (q*r).den ≤ q.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos q.pos r.pos) (Rat.mul_den_dvd q r)
  have hn' := log2_le_of_le_mul hn
  have hd' := log2_le_of_le_mul hd
  unfold ratBits
  omega

@[simp] theorem ratBits_inv_eq (q : ℚ) : ratBits q⁻¹ = ratBits q := by
  by_cases h : q.num = 0
  · rw [Rat.zero_of_num_zero h, inv_zero]
  · simp [ratBits, Rat.den_inv, h, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero h,
      Nat.add_comm, Nat.add_left_comm]

@[simp] theorem ratBits_one_value : ratBits 1 = 3 := rfl

theorem ratBits_natPow_le (q : ℚ) (n : ℕ) : ratBits (q^n) ≤ 3 + n * ratBits q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul, ← Nat.add_assoc]
    exact (ratBits_mul_le_add _ _).trans (Nat.add_le_add_right ih _)

theorem ratBits_intPow_le (q : ℚ) (z : ℤ) : ratBits (q^z) ≤ 3 + z.natAbs * ratBits q := by
  cases z with
  | ofNat n => simpa using ratBits_natPow_le q n
  | negSucc n => simpa [zpow_negSucc] using ratBits_natPow_le q (n+1)

/-- This applies in particular to every partial product taken while accumulating the factors. -/
theorem ratBits_partial_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ratBits (∏ i ∈ s, f i) ≤ 3 + ∑ i ∈ s, ratBits (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (ratBits_mul_le_add _ _).trans (by omega)

theorem ratBits_weighted_product_le {ι : Type*} (s : Finset ι) (x : ι → ℚ) (e : ι → ℤ)
    (k : ℤ) : ratBits ((2 : ℚ)^k * ∏ i ∈ s, (x i)^(e i)) ≤
      9 + 4 * k.natAbs + ∑ i ∈ s, (3 + (e i).natAbs * ratBits (x i)) := by
  have ht : ratBits 2 = 4 := rfl
  have h₀ := ratBits_intPow_le 2 k
  rw [ht, Nat.mul_comm] at h₀
  have h₁ := (ratBits_partial_prod_le s (fun i => (x i)^(e i))).trans
    (Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => ratBits_intPow_le (x i) (e i))) 3)
  exact (ratBits_mul_le_add _ _).trans (by omega)

/-- Explicit binary-size bound for the paper's entire sign-query product on the large-log branch. -/
theorem ratBits_proxyProduct_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ)
    (K E B : ℕ) (hk : (clearedProxyOffset large D c a grid).natAbs ≤ K)
    (he : ∀ i ∈ large, ((D : ℤ) * a i).natAbs ≤ E)
    (hb : ∀ i ∈ large, ratBits (mag i) ≤ B) :
    ratBits (proxyProduct large D c a grid mag) ≤ 9 + 4 * K + large.card * (3 + E * B) := by
  apply (ratBits_weighted_product_le large mag (fun i => (D : ℤ) * a i) _).trans
  apply Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) 9)
  simpa using Finset.sum_le_sum (s := large) (g := fun _ => 3 + E * B)
    (fun i hi => Nat.add_le_add_left (Nat.mul_le_mul (he i hi) (hb i hi)) 3)

/-- The exponent encoded by least-significant-bit-first input. -/
def exponentDigits : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (exponentDigits bs)

@[simp] theorem exponentDigits_bits (n : ℕ) : exponentDigits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h, exponentDigits, ih]

/-- Square-and-multiply. The trace stores newly computed scalar values, last operation first. -/
def binaryPowerTrace (q : ℚ) : List Bool → ℚ × List ℚ
  | [] => (1, [])
  | false :: bs =>
      let p := binaryPowerTrace q bs
      let sq := p.1 * p.1
      (sq, sq :: p.2)
  | true :: bs =>
      let p := binaryPowerTrace q bs
      let sq := p.1 * p.1
      let value := sq * q
      (value, value :: sq :: p.2)

theorem binaryPowerTrace_value (q : ℚ) (bs : List Bool) :
    (binaryPowerTrace q bs).1 = q ^ exponentDigits bs := by
  induction bs with
  | nil => simp [exponentDigits, binaryPowerTrace]
  | cons b bs ih =>
    cases b <;> simp [exponentDigits, binaryPowerTrace, Nat.bit_val, two_mul, pow_add, ih]

theorem binaryPowerTrace_length (q : ℚ) (bs : List Bool) :
    (binaryPowerTrace q bs).2.length ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [binaryPowerTrace]
  | cons b bs ih => cases b <;> simp only [binaryPowerTrace, List.length_cons] <;> omega

theorem binaryPowerTrace_intermediate (q : ℚ) (bs : List Bool) :
    ∀ z ∈ (binaryPowerTrace q bs).2, ∃ k ≤ exponentDigits bs, z = q^k := by
  induction bs with
  | nil => simp [binaryPowerTrace]
  | cons b bs ih =>
    have hp := binaryPowerTrace_value q bs
    have hsq : (binaryPowerTrace q bs).1 * (binaryPowerTrace q bs).1 =
        q^(2 * exponentDigits bs) := by rw [hp, two_mul, pow_add]
    intro z hz
    cases b with
    | false =>
      change z ∈ _ :: (binaryPowerTrace q bs).2 at hz
      rcases List.mem_cons.mp hz with he | h
      · exact ⟨_, by simp [exponentDigits, Nat.bit_val], he.trans hsq⟩
      · obtain ⟨k, hk, hval⟩ := ih z h
        exact ⟨k, by simp [exponentDigits, Nat.bit_val]; omega, hval⟩
    | true =>
      change z ∈ _ :: _ :: (binaryPowerTrace q bs).2 at hz
      rcases List.mem_cons.mp hz with he | h
      · exact ⟨_, le_rfl, he.trans (binaryPowerTrace_value q (true::bs))⟩
      · rcases List.mem_cons.mp h with he | h'
        · exact ⟨_, by simp [exponentDigits, Nat.bit_val], he.trans hsq⟩
        · obtain ⟨k, hk, hval⟩ := ih z h'
          exact ⟨k, by simp [exponentDigits, Nat.bit_val]; omega, hval⟩

/-- One reciprocal suffices for a negative exponent. -/
def signedPowerTrace (q : ℚ) : ℤ → ℚ × List ℚ
  | .ofNat n => binaryPowerTrace q n.bits
  | .negSucc n =>
      let p := binaryPowerTrace q (n+1).bits
      (p.1⁻¹, p.1⁻¹ :: p.2)

theorem signedPowerTrace_value (q : ℚ) (e : ℤ) : (signedPowerTrace q e).1 = q^e := by
  cases e <;> simp [signedPowerTrace, binaryPowerTrace_value, zpow_negSucc]

/-- The number of generated rational arithmetic results is logarithmic in the exponent. -/
theorem signedPowerTrace_length (q : ℚ) (e : ℤ) :
    (signedPowerTrace q e).2.length ≤ 2 * e.natAbs.size + 1 := by
  cases e with
  | ofNat n =>
    simpa [signedPowerTrace, Nat.size_eq_bits_len] using
      (binaryPowerTrace_length q n.bits).trans (Nat.le_succ _)
  | negSucc n =>
    simpa [signedPowerTrace, Nat.size_eq_bits_len] using
      Nat.succ_le_succ (binaryPowerTrace_length q (n+1).bits)

/-- Every scalar created by the powering algorithm itself meets the same polynomial
input-length bound as the final rational, including its final reciprocal. -/
theorem signedPowerTrace_intermediate (q : ℚ) (e : ℤ) :
    ∀ z ∈ (signedPowerTrace q e).2, ratBits z ≤ 3 + e.natAbs * ratBits q := by
  have hpos (n : ℕ) (z : ℚ) (hz : z ∈ (binaryPowerTrace q n.bits).2) :
      ratBits z ≤ 3 + n * ratBits q := by
    obtain ⟨k, hk, rfl⟩ := binaryPowerTrace_intermediate q n.bits z hz
    rw [exponentDigits_bits] at hk
    exact (ratBits_natPow_le q k).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  cases e with
  | ofNat n => exact hpos n
  | negSucc n =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | h
    · simpa [ratBits_inv_eq, binaryPowerTrace_value] using
        ratBits_natPow_le q (n+1)
    · exact hpos (n+1) z h

/-- Multiply a finite sequence of powers. The returned trace contains every rational
multiplication and reciprocal, in reverse evaluation order. -/
def powerProductTrace : List (ℚ × ℤ) → ℚ × List ℚ
  | [] => (1, [])
  | (q,e) :: ps =>
      let previous := powerProductTrace ps
      let factor := signedPowerTrace q e
      let value := factor.1 * previous.1
      (value, value :: (factor.2 ++ previous.2))

theorem powerProductTrace_value (ps : List (ℚ × ℤ)) :
    (powerProductTrace ps).1 = (ps.map fun p => p.1 ^ p.2).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨q, e⟩
    simp [powerProductTrace, signedPowerTrace_value, ih]

theorem powerProductTrace_length (ps : List (ℚ × ℤ)) :
    (powerProductTrace ps).2.length ≤ (ps.map fun p => 2 * p.2.natAbs.size + 2).sum := by
  induction ps with
  | nil => simp [powerProductTrace]
  | cons p ps ih =>
    rcases p with ⟨q, e⟩
    simp only [powerProductTrace, List.length_cons, List.length_append,
      List.map_cons, List.sum_cons]
    have h := signedPowerTrace_length q e
    omega

/-- A single linear expression bounds the accumulated product and every intermediate in
the entire computation, including intermediate powers, reciprocals and partial products. -/
theorem powerProductTrace_bitBounds (ps : List (ℚ × ℤ)) :
    ratBits (powerProductTrace ps).1 ≤ 3 + (ps.map fun p => 3 + p.2.natAbs * ratBits p.1).sum ∧
    ∀ z ∈ (powerProductTrace ps).2, ratBits z ≤
      3 + (ps.map fun p => 3 + p.2.natAbs * ratBits p.1).sum := by
  induction ps with
  | nil => simp [powerProductTrace]
  | cons p ps ih =>
    rcases p with ⟨q, e⟩
    let budget := (ps.map fun p => 3 + p.2.natAbs * ratBits p.1).sum
    have h₁ : ratBits (powerProductTrace ps).1 ≤ 3 + budget := ih.1
    have h₂ : ratBits (signedPowerTrace q e).1 ≤ 3 + e.natAbs * ratBits q := by
      simpa only [signedPowerTrace_value] using ratBits_intPow_le q e
    have h₃ := ratBits_mul_le_add (signedPowerTrace q e).1 (powerProductTrace ps).1
    have hval : ratBits ((signedPowerTrace q e).1 * (powerProductTrace ps).1) ≤
        3 + (3 + e.natAbs * ratBits q + budget) := by omega
    refine ⟨hval, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hval
    · change ratBits z ≤ 3 + (3 + e.natAbs * ratBits q + budget)
      rcases List.mem_append.mp hz with h | h
      · have := signedPowerTrace_intermediate q e z h
        omega
      · have : ratBits z ≤ 3 + budget := ih.2 z h
        omega

/-- Run the comparison's powers on an enumeration of the large indices. The proofs
hold for any order in which those indices are enumerated. -/
noncomputable def proxyPowerTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) : ℚ × List ℚ :=
  powerProductTrace ((2, clearedProxyOffset large D c a grid) ::
    large.toList.map fun i => (mag i, (D : ℤ) * a i))

theorem proxyPowerTrace_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) :
    (proxyPowerTrace large D c a grid mag).1 = proxyProduct large D c a grid mag := by
  simp [proxyPowerTrace, powerProductTrace_value, List.map_map, Function.comp_def,
    Finset.prod_map_toList, proxyProduct]

theorem proxyPowerTrace_length {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) :
    (proxyPowerTrace large D c a grid mag).2.length ≤
      2 * (clearedProxyOffset large D c a grid).natAbs.size + 2 +
      ∑ i ∈ large, (2 * ((D : ℤ) * a i).natAbs.size + 2) := by
  simpa [proxyPowerTrace, List.map_map, Function.comp_def, Finset.sum_map_toList] using
    powerProductTrace_length ((2, clearedProxyOffset large D c a grid) ::
      large.toList.map fun i => (mag i, (D : ℤ) * a i))

theorem proxyPowerTrace_intermediate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ)
    (K E B : ℕ) (hk : (clearedProxyOffset large D c a grid).natAbs ≤ K)
    (he : ∀ i ∈ large, ((D : ℤ) * a i).natAbs ≤ E)
    (hb : ∀ i ∈ large, ratBits (mag i) ≤ B) :
    ∀ z ∈ (proxyPowerTrace large D c a grid mag).2,
      ratBits z ≤ 6 + 4 * K + large.card * (3 + E * B) := by
  intro z hz
  have h := (powerProductTrace_bitBounds ((2, clearedProxyOffset large D c a grid) ::
    large.toList.map fun i => (mag i, (D : ℤ) * a i))).2 z hz
  have h₂ : ratBits 2 = 4 := rfl
  simp [h₂, List.map_map, Function.comp_def, Finset.sum_map_toList] at h
  have hsum : ∑ i ∈ large, (3 + ((D : ℤ)*a i).natAbs * ratBits (mag i)) ≤
      large.card * (3 + E*B) := by
    simpa using Finset.sum_le_sum (s := large) (g := fun _ => 3 + E*B)
      (fun i hi => Nat.add_le_add_left (Nat.mul_le_mul (he i hi) (hb i hi)) 3)
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
