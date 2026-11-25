import OAI.LinearAlgebra.SpectralBooks.Batcher
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.ModularMultiply

namespace OAI
/-! # Batcher sorting on bounded-width Boolean records

A record is an unsigned word in little-endian representation. Fields in the more significant
bits take precedence, and a compare-exchange moves all the bits of each record together.
The physical circuit uses bounded-fan-in Boolean nodes and static routing.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

open ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork ExactQuantumFactoring.BitArithmetic

/-- Bits of a single unsigned record, least significant first. -/
def wordBits {w : ℕ} (x : Fin (2^w)) : Basis w := fun i ↦ (BitVec.ofFin x).getLsbD i.val

/-- Consecutive fixed-width records in a single Boolean input or output. -/
def encodeWords {r w : ℕ} (x : Fin r → Fin (2^w)) : Basis (r*w) :=
  fun b ↦ wordBits (x (finProdFinEquiv.symm b).1) (finProdFinEquiv.symm b).2

@[simp] theorem encodeWords_at {r w : ℕ} (x : Fin r → Fin (2^w)) (i : Fin r) (j : Fin w) :
    encodeWords x (finProdFinEquiv (i,j)) = wordBits (x i) j := by simp [encodeWords]

@[simp] theorem bitsValue_wordBits {w : ℕ} (x : Fin (2^w)) :
    bitsValue (wordBits x) = BitVec.ofFin x := bitsValue_bits _

/-- Recover the unsigned records on arbitrary raw Boolean wires. -/
def decodeWords {r w : ℕ} (z : Basis (r*w)) (i : Fin r) : Fin (2^w) :=
  (bitsValue (fun j ↦ z (finProdFinEquiv (i,j)))).toFin

@[simp] theorem encodeWords_decodeWords {r w : ℕ} (z : Basis (r*w)) :
    encodeWords (decodeWords z) = z := by
  funext b
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective b
  rw [encodeWords_at]
  exact bitsValue_bit _ j

@[simp] theorem decodeWords_encodeWords {r w : ℕ} (x : Fin r → Fin (2^w)) :
    decodeWords (encodeWords x) = x := by
  funext i
  simp [decodeWords]

/-- Free selection, repetition, or permutation of whole records. -/
def selectRows {r s : ℕ} (w : ℕ) (f : Fin r → Fin s) : BooleanNetwork (s*w) (r*w) :=
  select (fun b ↦ finProdFinEquiv (f (finProdFinEquiv.symm b).1, (finProdFinEquiv.symm b).2))

@[simp] theorem selectRows_eval {r s w : ℕ} (f : Fin r → Fin s) (x : Fin s → Fin (2^w)) :
    (selectRows w f).eval (encodeWords x) = encodeWords (x ∘ f) := by
  funext b
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [selectRows, eval_select, Function.comp_apply, Equiv.symm_apply_apply, encodeWords_at]

private def selectWord {r : ℕ} (w : ℕ) (i : Fin r) : BooleanNetwork (r*w) w :=
  select (fun j ↦ finProdFinEquiv (i,j))

private theorem selectWord_eval {r w : ℕ} (i : Fin r) (x : Fin r → Fin (2^w)) :
    (selectWord w i).eval (encodeWords x) = wordBits (x i) := by
  funext j
  exact encodeWords_at x i j

/-- Gather two disjoint output blocks. Each argument circuit is instantiated once. -/
private def joinNets {n k w : ℕ} (l r : BooleanNetwork n (2^k*w)) :
    BooleanNetwork n (2^(k+1)*w) :=
  (l.pair r).rewire (fun b ↦
    join (fun i j ↦ (finProdFinEquiv (i,j)).castAdd (2^k*w))
      (fun i j ↦ Fin.natAdd (2^k*w) (finProdFinEquiv (i,j)))
      (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2)

private theorem joinNets_eval {n k w : ℕ} (l r : BooleanNetwork n (2^k*w))
    (z : Basis n) (x y : Wires k (Fin (2^w))) (hl : l.eval z = encodeWords x)
    (hr : r.eval z = encodeWords y) :
    (joinNets l r).eval z = encodeWords (join x y) := by
  funext b
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective b
  rcases low_or_high i with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
    simp only [joinNets, eval_rewire, eval_pair, Function.comp_apply, Equiv.symm_apply_apply,
      join_low, join_high, hl, hr, Fin.append_left, Fin.append_right, encodeWords_at]

private theorem joinNets_count {n k w : ℕ} (l r : BooleanNetwork n (2^k*w)) :
    (joinNets l r).net.count = l.net.count + r.net.count := count_pair l r

/-- Bundle whole word outputs without replicating their computation at each bit. -/
def gatherWords {n w : ℕ} : {k : ℕ} → Wires k (BooleanNetwork n w) →
    BooleanNetwork n (2^k*w)
  | 0, f => (f 0).rewire (fun b ↦ (finProdFinEquiv.symm b).2)
  | k+1, f => joinNets (k := k) (gatherWords (f ∘ low)) (gatherWords (f ∘ high))

theorem gatherWords_eval {n k w : ℕ} (f : Wires k (BooleanNetwork n w)) (z : Basis n)
    (x : Wires k (Fin (2^w))) (hf : ∀ i, (f i).eval z = wordBits (x i)) :
    (gatherWords f).eval z = encodeWords x := by
  induction k with
  | zero =>
    funext b
    obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective b
    have hi : i = 0 := Fin.ext (by have h := i.isLt; simp only [pow_zero] at h; exact Nat.lt_one_iff.mp h)
    simp only [gatherWords, eval_rewire, Function.comp_apply, Equiv.symm_apply_apply, hf, encodeWords_at, hi]
  | succ k ih =>
    have hx : join (x ∘ low) (x ∘ high) = x := by
      funext i
      rcases low_or_high i with ⟨j,rfl⟩ | ⟨j,rfl⟩ <;> simp
    exact (joinNets_eval _ _ z (x ∘ low) (x ∘ high)
      (ih _ _ (fun i ↦ hf (low i))) (ih _ _ (fun i ↦ hf (high i)))).trans (congrArg encodeWords hx)

theorem gatherWords_count {n k w c : ℕ} (f : Wires k (BooleanNetwork n w))
    (hf : ∀ i, (f i).net.count ≤ c) : (gatherWords f).net.count ≤ 2^k*c := by
  induction k with
  | zero => simpa [gatherWords] using hf 0
  | succ k ih =>
    rw [gatherWords, joinNets_count]
    calc
      _ ≤ 2^k*c + 2^k*c := Nat.add_le_add (ih _ (fun i ↦ hf (low i))) (ih _ (fun i ↦ hf (high i)))
      _ = _ := by rw [pow_succ]; ring

/-- One output of a compare-exchange on the indicated records. The selector is shared
by every bit moved into this output. -/
private def compareWord {r : ℕ} (w : ℕ) (small : Bool) (i j : Fin r) :
    BooleanNetwork (r*w) w :=
  let a := selectWord w i
  let b := selectWord w j
  if small then wordMux (wordLe a b) a b else wordMux (wordLe a b) b a

private theorem compareWord_eval {r w : ℕ} (small : Bool) (i j : Fin r)
    (x : Fin r → Fin (2^w)) :
    (compareWord w small i j).eval (encodeWords x) =
      wordBits (if small then min (x i) (x j) else max (x i) (x j)) := by
  cases small <;>
    simp [compareWord, wordMux_eval, wordLe_eval, selectWord_eval]
  all_goals
    by_cases h : x i ≤ x j
    · simp [h]
    · have h' := le_of_not_ge h
      simp [h, min_eq_right h', max_eq_left h']

private theorem compareWord_count {r : ℕ} (w : ℕ) (small : Bool) (i j : Fin r) :
    (compareWord w small i j).net.count ≤ 55*w+9 := by
  have h := wordLe_count (selectWord w i) (selectWord w j)
  cases small <;> simp [compareWord, wordMux_count, selectWord] at * <;> omega

/-- Compile an arbitrary Batcher schedule on fixed-width words to Boolean gates. -/
def Network.boolean {k : ℕ} (w : ℕ) : Network k → BooleanNetwork (2^k*w) (2^k*w)
  | .nil => select id
  | .reverse => selectRows w Fin.rev
  | .compareHalves (k := d) =>
    joinNets (k := d) (gatherWords (fun i ↦ compareWord w true (low i) (high i)))
      (gatherWords (fun i ↦ compareWord w false (low i) (high i)))
  | .parallel (k := d) l r =>
    joinNets (k := d) ((selectRows w low).comp (l.boolean w))
      ((selectRows w high).comp (r.boolean w))
  | .seq a b => (a.boolean w).comp (b.boolean w)

theorem Network.boolean_eval {k w : ℕ} (N : Network k) (x : Wires k (Fin (2^w))) :
    (N.boolean w).eval (encodeWords x) = encodeWords (N.eval x) := by
  induction N with
  | nil => rfl
  | reverse => exact selectRows_eval Fin.rev x
  | compareHalves =>
    apply joinNets_eval
    · apply gatherWords_eval
      intro i
      exact compareWord_eval true _ _ _
    · apply gatherWords_eval
      intro i
      exact compareWord_eval false _ _ _
  | parallel l r hl hr =>
    apply joinNets_eval <;> rw [BooleanNetwork.eval_comp, selectRows_eval]
    · exact hl _
    · exact hr _
  | seq a b ha hb => simp only [Network.boolean, Network.eval, BooleanNetwork.eval_comp, ha, hb]

theorem Network.boolean_count {k : ℕ} (N : Network k) (w : ℕ) :
    (N.boolean w).net.count ≤ N.comparisons*(110*w+18) := by
  induction N with
  | nil | reverse => simp [Network.boolean, Network.comparisons, selectRows]
  | @compareHalves d =>
    rw [Network.boolean, joinNets_count, Network.comparisons]
    have h (small : Bool) := gatherWords_count (k := d)
      (fun i ↦ compareWord w small (low i) (high i)) (fun i ↦ compareWord_count w small _ _)
    calc
      _ ≤ 2^d*(55*w+9) + 2^d*(55*w+9) := Nat.add_le_add (h true) (h false)
      _ = _ := by ring
  | parallel l r hl hr =>
    simpa [Network.boolean, joinNets_count, count_comp, selectRows, Network.comparisons,
      Nat.add_mul] using Nat.add_le_add hl hr
  | seq a b ha hb =>
    simpa [Network.boolean, count_comp, Network.comparisons, Nat.add_mul] using Nat.add_le_add ha hb

/-- Boolean circuit sorting an entire batch of `2^k` unsigned words. -/
def booleanSort (k w : ℕ) : BooleanNetwork (2^k*w) (2^k*w) := (sortNet k).boolean w

theorem booleanSort_eval {k w : ℕ} (x : Wires k (Fin (2^w))) :
    (booleanSort k w).eval (encodeWords x) = encodeWords ((sortNet k).eval x) :=
  (sortNet k).boolean_eval x

/-- A linear price per word exchange gives a quasilinear gate count in the number of rows. -/
theorem booleanSort_count (k w : ℕ) :
    (booleanSort k w).net.count ≤ (2^k*k*(k+1)/4)*(110*w+18) := by
  rw [← Nat.eq_div_of_mul_eq_right (by decide : 4 ≠ 0) (sortNet_comparisons k)]
  exact (sortNet k).boolean_count w

/-- The circuit returns an ordered permutation, with all payload bits and ties preserved. -/
theorem booleanSort_correct {k w : ℕ} (x : Wires k (Fin (2^w))) :
    ∃ e : Equiv.Perm (Fin (2^k)), Monotone (x ∘ e) ∧
      (booleanSort k w).eval (encodeWords x) = encodeWords (x ∘ e) := by
  obtain ⟨hs, e, he⟩ := sortNet_correct x
  exact ⟨e, he ▸ hs, (booleanSort_eval x).trans (congrArg encodeWords he)⟩

/-- Sorting arbitrary raw records orders their key in the high bits; the same permutation
transports every low-bit payload with its key. -/
theorem booleanSort_key {k w : ℕ} (payloadBits : ℕ) (z : Basis (2^k*w)) :
    ∃ e : Equiv.Perm (Fin (2^k)),
      decodeWords ((booleanSort k w).eval z) = decodeWords z ∘ e ∧
      Monotone (fun i ↦ (decodeWords z (e i)).val / 2^payloadBits) := by
  obtain ⟨e, hmono, hout⟩ := booleanSort_correct (decodeWords z)
  refine ⟨e, ?_, fun i j hij ↦ Nat.div_le_div_right (hmono hij)⟩
  rw [encodeWords_decodeWords] at hout
  rw [hout, decodeWords_encodeWords]

end LinearAlgebra.SpectralBooks.Batcher

end OAI
