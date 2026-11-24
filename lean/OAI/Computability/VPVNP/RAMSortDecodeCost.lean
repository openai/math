import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Tactic.FinCases

/-!
# Word work to decode a sorting record

The validator of Lemma 10.1 receives five little-endian words per record. The scan below
visits the most significant remaining bit, doubles the accumulator, and adds the bit.
The decoder retains the five results, parses their tag and checks the resulting canonical
words. Its bound applies to every bit field, including unknown tags and malformed padding.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

open BurstRAM RAMSerialization

variable {w : ℕ}

/-- The first component is the decoded value. The second counts word operations. At each
bit charge the loop test, decrement, offset arithmetic, bit load, doubling, addition and
loop branch. Offset arithmetic has two operations, giving eight in total. The final zero
counter test costs one. -/
private def scanFrom (b : Fin w → Bool) : (k : ℕ) → k ≤ w → ℕ → ℕ × ℕ
  | 0, _, acc => (acc, 1)
  | k + 1, hk, acc =>
    let bit := b ⟨k, hk⟩
    let r := scanFrom b k (by omega) (acc + acc + bit.toNat)
    (r.1, 8 + r.2)

private theorem scanFrom_steps (b : Fin w → Bool) (k : ℕ) (hk : k ≤ w) (acc : ℕ) :
    (scanFrom b k hk acc).2 = 8 * k + 1 := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih => simp only [scanFrom, ih]; omega

/-- After `w-k-1` bits, doubling the accumulator and adding a bit fits in `w-k` bits.
Thus all intermediate results of the scan from zero fit in a single `w`-bit word. -/
theorem scan_digit_fits {k acc : ℕ} (hk : k + 1 ≤ w) (ha : acc < 2 ^ (w - (k + 1))) (bit : Bool) :
    acc + acc + bit.toNat < 2 ^ (w - k) := by
  rw [show w - k = (w - (k + 1)) + 1 by omega, Nat.pow_succ]
  cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem scanFrom_value (b : Fin w → Bool) (k : ℕ) (hk : k ≤ w) (acc : ℕ) :
    (scanFrom b k hk acc).1 = acc * 2 ^ k + ∑ i : Fin k, (b ⟨i, i.isLt.trans_le hk⟩).toNat * 2 ^ (i : ℕ) := by
  induction k generalizing acc with
  | zero => simp [scanFrom]
  | succ k ih =>
    rw [scanFrom, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.pow_succ, Nat.add_mul, ← Nat.mul_assoc]
    omega

private theorem inverse_word_value (b : Fin w → Bool) :
    ((wordBits w).symm b).val = ∑ i, (b i).toNat * 2 ^ (i : ℕ) := by
  change (finFunctionFinEquiv (fun i ↦ finTwoEquiv.symm (b i)) : ℕ) = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases h : b i <;> rfl

/-- Decode a word once. Charge the initialization of the cursor and accumulator. -/
def scanWord (b : Fin w → Bool) : Word w × ℕ :=
  let result := scanFrom b w le_rfl 0
  (⟨result.1, by
      rw [scanFrom_value, Nat.zero_mul, Nat.zero_add, ← inverse_word_value b]
      exact ((wordBits w).symm b).isLt⟩, result.2 + 2)

theorem scanWord_eq (b : Fin w → Bool) : (scanWord b).1 = (wordBits w).symm b := by
  apply Fin.ext
  simp [scanWord, scanFrom_value, inverse_word_value]

@[simp] theorem scanWord_steps (b : Fin w → Bool) : (scanWord b).2 = 8 * w + 3 := by
  simp [scanWord, scanFrom_steps, Nat.add_assoc]

/-- Read the tag register, compare against up to three known tags, and copy four
payload registers into the parsed record. Each failed comparison costs a compare and a
branch. Unknown tags reach the empty-record candidate and are checked below. -/
private def parseSaved (a : Fin 5 → Word w) : Option (WordRecord w) × ℕ :=
  let tag := (a 0).val
  let mk := fun k ↦ some (WordRecord.mk k (a 1) (a 2) (a 3) (a 4))
  if tag = 1 then (mk .init, 8)
  else if tag = 2 then (mk .read, 10)
  else if tag = 3 then (mk .write, 12)
  else (none, 8)

private theorem parseSaved_eq (hw : 2 ≤ w) (a : Fin 5 → Word w) :
    (parseSaved a).1 = (recordFormat hw).parse a := by
  simp only [parseSaved, recordFormat]
  generalize (a 0).val = tag
  match tag with
  | 0 | 1 | 2 | 3 | _ + 4 => rfl

private theorem parseSaved_steps (a : Fin 5 → Word w) : (parseSaved a).2 ≤ 12 := by
  dsimp only [parseSaved]
  split_ifs <;> dsimp <;> decide

/-- Check canonical fields from the highest remaining register downwards. A failed word
comparison exits immediately. Charge the loop test, decrement, two loads, equality and
branch on each iteration, and one test for an empty prefix. -/
private def checkPrefix (a b : Fin 5 → Word w) : (k : ℕ) → k ≤ 5 → Bool × ℕ
  | 0, _ => (true, 1)
  | k + 1, hk =>
    if a ⟨k, hk⟩ = b ⟨k, hk⟩ then
      let r := checkPrefix a b k (by omega)
      (r.1, 6 + r.2)
    else (false, 6)

private theorem checkPrefix_spec (a b : Fin 5 → Word w) (k : ℕ) (hk : k ≤ 5) :
    (checkPrefix a b k hk).1 = true ↔ ∀ i : Fin 5, i.val < k → a i = b i := by
  induction k with
  | zero => simp [checkPrefix]
  | succ k ih =>
    rw [checkPrefix]
    split
    · rename_i he
      rw [ih]
      constructor
      · intro hall i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
        · exact hall i h
        · exact (Fin.ext h : i = ⟨k, hk⟩) ▸ he
      · exact fun hall i hi ↦ hall i (Nat.lt_succ_of_lt hi)
    · rename_i hne
      simp only [Bool.false_eq_true, false_iff]
      exact fun hall ↦ hne (hall ⟨k, hk⟩ (Nat.lt_succ_self k))

private theorem checkPrefix_steps (a b : Fin 5 → Word w) (k : ℕ) (hk : k ≤ 5) :
    (checkPrefix a b k hk).2 ≤ 6 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [checkPrefix]
    split <;> dsimp
    · have := ih (by omega)
      omega
    · omega

/-- The `5*w` physical bits split into five successive word streams. -/
private def readField (b : Fin (5 * w) → Bool) (i : Fin 5) : Word w × ℕ :=
  scanWord (fun j ↦ b (finProdFinEquiv (i, j)))

private theorem readField_eq (b : Fin (5 * w) → Bool) (i : Fin 5) :
    (readField b i).1 = (arrayBits 5 w).symm b i := by
  rw [readField, scanWord_eq]
  apply (wordBits w).injective
  funext j
  rw [Equiv.apply_symm_apply]
  rw [← arrayBits_at, Equiv.apply_symm_apply]

/-- Scan the five words into registers and run the tag and canonical-field checks.
In addition to their measured costs, charge five register writes, ten operations for
dispatch and writing the five canonical words, and two for the final branch and return.
`some none` is the canonical empty record, and `none` rejects. -/
def decodeSlot (hw : 2 ≤ w) (b : Fin (5 * w) → Bool) : Option (Option (WordRecord w)) × ℕ :=
  let f₀ := readField b 0
  let f₁ := readField b 1
  let f₂ := readField b 2
  let f₃ := readField b 3
  let f₄ := readField b 4
  let a := ![f₀.1, f₁.1, f₂.1, f₃.1, f₄.1]
  let parsed := parseSaved a
  let check := checkPrefix ((recordFormat hw).words parsed.1) a 5 le_rfl
  (if check.1 then some parsed.1 else none,
    f₀.2 + f₁.2 + f₂.2 + f₃.2 + f₄.2 + 5 + parsed.2 + 10 + check.2 + 2)

/-- The bounded decoder and the message format agree for every input bit string. -/
theorem decodeSlot_eq (hw : 2 ≤ w) (b : Fin (5 * w) → Bool) :
    (decodeSlot hw b).1 = (recordFormat hw).decode b := by
  let a := (arrayBits 5 w).symm b
  have hv : ![(readField b 0).1, (readField b 1).1, (readField b 2).1, (readField b 3).1,
      (readField b 4).1] = a := by
    funext i
    fin_cases i <;> apply readField_eq
  have hcheck (u v : Fin 5 → Word w) : (checkPrefix u v 5 le_rfl).1 = true ↔ u = v := by
    rw [checkPrefix_spec]
    exact ⟨fun h ↦ funext (fun i ↦ h i i.isLt), fun h _ _ ↦ congrFun h _⟩
  simp only [decodeSlot, hv, Format.decode, hcheck, parseSaved_eq hw, Format.encode]
  have hc (x : Fin 5 → Word w) : arrayBits 5 w x = b ↔ x = a :=
    (arrayBits 5 w).eq_symm_apply.symm
  simp only [hc]
  rfl

theorem decodeSlot_cost (hw : 2 ≤ w) (b : Fin (5 * w) → Bool) :
    (decodeSlot hw b).2 ≤ 64 * (w + 1) := by
  simp only [decodeSlot, readField, scanWord_steps]
  have hp := parseSaved_steps (w := w)
  have hc (a b : Fin 5 → Word w) := checkPrefix_steps a b 5 le_rfl
  grw [hp, hc]
  omega

end RAMSort

end VPVNP
end Computability
end OAI
