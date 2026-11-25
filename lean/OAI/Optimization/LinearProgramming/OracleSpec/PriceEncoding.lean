import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size
import Lean.Elab.Tactic.Omega

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

/-- Concatenated framed words have a unique first component and remainder. -/
theorem frame_prefix (u v x y : Word) : frame u ++ x = frame v ++ y ↔ u = v ∧ x = y := by
  induction u generalizing v with
  | nil => cases v <;> simp [frame]
  | cons b bs ih =>
    cases v with
    | nil => simp [frame]
    | cons b' bs' =>
      change true :: b :: (frame bs ++ x) = true :: b' :: (frame bs' ++ y) ↔ _
      simp only [List.cons.injEq, true_and, ih]
      tauto

theorem frame_length (w : Word) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
    change (frame bs).length + 1 + 1 = _
    rw [ih, List.length_cons]
    omega

theorem natBits_decode (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih => simp [Nat.bits_append_bit _ _ hn, ih]

/-- Writing an integer costs linear time in its binary length in this format. -/
theorem encodeNat_length (n : ℕ) : (encodeNat n).length = 2 * n.size + 1 := by
  rw [encodeNat, frame_length, Nat.size_eq_bits_len]

theorem encodeNat_prefix (n m : ℕ) (x y : Word) :
    encodeNat n ++ x = encodeNat m ++ y ↔ n = m ∧ x = y := by
  rw [encodeNat, encodeNat, frame_prefix]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by simpa only [natBits_decode] using congrArg (List.foldr Nat.bit 0) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem encodeRat_prefix (q r : ℚ) (x y : Word) :
    encodeRat q ++ x = encodeRat r ++ y ↔ q = r ∧ x = y := by
  constructor
  · intro h
    simp only [encodeRat, List.cons_append, List.cons.injEq, List.append_assoc,
      encodeNat_prefix] at h
    obtain ⟨hs, hm, hd, hx⟩ := h
    refine ⟨Rat.ext ?_ hd, hx⟩
    rcases Int.natAbs_eq_natAbs_iff.mp hm with h | h
    · exact h
    · have signs : (q.num < 0 ↔ r.num < 0) := decide_eq_decide.mp hs
      by_cases hq : q.num < 0
      · have hr := signs.mp hq
        omega
      · have hr := mt signs.mpr hq
        omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem encodeRats_prefix (qs rs : List ℚ) (h : qs.length = rs.length) (x y : Word) :
    qs.flatMap encodeRat ++ x = rs.flatMap encodeRat ++ y ↔ qs = rs ∧ x = y := by
  induction qs generalizing rs with
  | nil => cases rs <;> simp_all
  | cons q qs ih =>
    cases rs with
    | nil => simp at h
    | cons r rs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.flatMap_cons, List.append_assoc, encodeRat_prefix, ih rs h,
        List.cons.injEq]
      tauto

/-- Every valid raw query has exactly one designated good and exactly one vector of prices. -/
theorem priceQuery_injective {N : ℕ} {i j : Fin N} {p q : Fin N → ℚ} :
    priceQuery i p = priceQuery j q ↔ i = j ∧ p = q := by
  rw [priceQuery, priceQuery, encodeNat_prefix]
  have h := encodeRats_prefix (List.ofFn p) (List.ofFn q) (by simp) [] []
  simpa only [List.append_nil, List.ofFn_inj, and_true, Fin.val_inj] using
    and_congr (Iff.rfl : i.val = j.val ↔ i.val = j.val) h

end OracleSpec
end LinearProgramming
end Optimization
end OAI
