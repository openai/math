import OAI.Optimization.LinearProgramming.Compression.MinorIndex
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.Pairing

/-! Keys for comparing requested minors. Constructing a key traverses only its own row
and column selections. The leading size also determines the number of following pairs. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

private def squareMinorKey {m n : ℕ} (u : SquareMinorIndex m n) : List ℕ :=
  u.1.val :: List.ofFn (fun j => Nat.pair (u.2.1 j).val (u.2.2 j).val)

private theorem squareMinorKey_injective {m n : ℕ} : Function.Injective (@squareMinorKey m n) := by
  rintro ⟨k,r,c⟩ ⟨l,t,d⟩ h
  obtain ⟨hk, hrest⟩ := List.cons.inj h
  obtain rfl := Fin.ext hk
  have hp := List.ofFn_injective hrest
  have he (j : Fin k.val) : (r j).val = (t j).val ∧ (c j).val = (d j).val :=
    Nat.pair_eq_pair.mp (congrFun hp j)
  have hr : r = t := DFunLike.ext _ _ fun j => Fin.ext (he j).1
  have hc : c = d := DFunLike.ext _ _ fun j => Fin.ext (he j).2
  rw [hr, hc]

/-- Matrix selector, minor size, and the pair of row/column positions at each location. -/
def pairMinorKey {rD rE n : ℕ} : PairMinorIndex rD rE n → List ℕ
  | .inl u => 0 :: squareMinorKey u
  | .inr u => 1 :: squareMinorKey u

theorem pairMinorKey_injective {rD rE n : ℕ} : Function.Injective (@pairMinorKey rD rE n) := by
  rintro (u | u) (v | v) h
  · exact congrArg Sum.inl (squareMinorKey_injective (List.cons.inj h).2)
  · exact (Nat.zero_ne_one (List.cons.inj h).1).elim
  · exact (Nat.one_ne_zero (List.cons.inj h).1).elim
  · exact congrArg Sum.inr (squareMinorKey_injective (List.cons.inj h).2)

/-- Lexicographic order is calculated on the two keys. Membership in the universe of minors
is never enumerated to decide a comparison. The subtype of nonzero minors inherits this order. -/
instance pairMinorIndexLinearOrder (rD rE n : ℕ) : LinearOrder (PairMinorIndex rD rE n) :=
  LinearOrder.lift' pairMinorKey pairMinorKey_injective

@[simp] theorem pairMinor_le_iff_keys_le {rD rE n : ℕ} (u v : PairMinorIndex rD rE n) :
    u ≤ v ↔ pairMinorKey u ≤ pairMinorKey v := Iff.rfl

theorem pairMinorKey_length_le {rD rE n : ℕ} (u : PairMinorIndex rD rE n) :
    (pairMinorKey u).length ≤ n + 2 := by
  cases u with
  | inl v => simp [pairMinorKey, squareMinorKey]; omega
  | inr v => simp [pairMinorKey, squareMinorKey]; omega

private theorem squareKey_entry_le {m n : ℕ} (hm : m ≤ n) (u : SquareMinorIndex m n)
    {x : ℕ} (hx : x ∈ squareMinorKey u) : x ≤ (n+1)^2 := by
  obtain ⟨k,r,c⟩ := u
  rcases List.mem_cons.mp hx with he | tail
  · change x = k.val at he
    rw [he]
    have hk := k.isLt
    nlinarith
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp tail
    refine (Nat.pair_lt_max_add_one_sq _ _).le.trans (Nat.pow_le_pow_left ?_ 2)
    exact Nat.succ_le_succ (max_le ((r j).isLt.le.trans hm) (c j).isLt.le)

theorem pairMinorKey_entry_le {rD rE n : ℕ} (hrows : rD + rE = n) (u : PairMinorIndex rD rE n)
    {x : ℕ} (hx : x ∈ pairMinorKey u) : x ≤ (n+1)^2 := by
  rcases u with u | u
  · rcases List.mem_cons.mp hx with rfl | ht
    · exact Nat.zero_le _
    · exact squareKey_entry_le (by omega) u ht
  · rcases List.mem_cons.mp hx with rfl | ht
    · exact Nat.one_le_pow _ _ (by omega)
    · exact squareKey_entry_le (by omega) u ht

private theorem keyBits_le_length (L : List ℕ) (b : ℕ) (h : ∀ x ∈ L, x ≤ b) :
    (L.map (fun x => x.log2 + 1)).sum ≤ L.length * (b+1) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := Nat.add_le_add_right (a.log2_le_self.trans (h a List.mem_cons_self)) 1
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add ha ht

/-- A polynomial bound on the sum of binary field lengths, including both header fields. -/
theorem pairMinorKey_bits_le {rD rE n : ℕ} (hrows : rD + rE = n) (u : PairMinorIndex rD rE n) :
    ((pairMinorKey u).map (fun x => x.log2 + 1)).sum ≤ (n+2)*((n+1)^2+1) :=
  (keyBits_le_length _ _ fun _ h => pairMinorKey_entry_le hrows u h).trans
    (Nat.mul_le_mul_right _ (pairMinorKey_length_le u))

end Compression
end LinearProgramming
end Optimization
end OAI
