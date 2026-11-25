import OAI.Computability.NearSquareRoot.PhaseProgramRelease
import OAI.Computability.NearSquareRoot.InterchangeSignMachine
import OAI.Computability.NearSquareRoot.SynchronizedRadixAddress
import OAI.Computability.IntegerMultiplication.Bits.Word

/-! # Short-address queries for the synchronized radix layers

A query contains a unary stage index and a most-significant-first address
of its full padded width. The reply gives the bit-reversed address, the
butterfly partner, the binary logarithm of the twiddle denominator in unary,
and its numerator in least-significant-first binary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RadixAddressTape

open IntegerMultiplication Code Bits

abbrev Query := Tally × Word
abbrev Reply := Word × Word × Tally × Word

private def inspectTail : Word → Word × Tally × Word := fun w =>
  List.casesOn w ([], [], []) fun b s =>
    ((!b) :: s, () :: ruler s, bif b then s.reverse else [])

def reply (q : Query) : Reply :=
  let p := cutLists q
  let t := inspectTail p.2
  (q.2.reverse, p.1 ++ t.1, t.2)

private theorem easy_inspectTail : Easy inspectTail := by
  let comp (p : Bool × Word) := (!p.1) :: p.2
  have flip : Easy comp :=
    ((Easy.fst.compose (Easy.finite Bool.not)).pair Easy.snd).compose Easy.cons
  have width : Easy (fun p : Bool × Word => () :: ruler p.2) :=
    ((Easy.const ()).pair (Easy.ruler Easy.snd)).compose Easy.cons
  have num : Easy (fun p : Bool × Word => bif p.1 then p.2.reverse else []) :=
    Easy.ifst (Easy.const _) Easy.reverse
  exact Easy.listCase _ (flip.pair (width.pair num))

/-- One fixed P192 stack program answers the three local radix address
queries together in linear time in the encoded input size. -/
theorem easy_reply : Easy reply := by
  have cut := easy_cut (Easy.identity (X := Query))
  have tail := cut.sndCompose.compose easy_inspectTail
  exact (Easy.snd.compose Easy.reverse).pair
    ((easy_append cut.fstCompose tail.fstCompose).pair tail.sndCompose)

def width (q : Query) : ℕ := q.1.length + q.2.length

private theorem query_size : Dom width (fun q : Query => size q) := by
  refine ⟨1, 3, fun q => ?_⟩
  simp [width, size_prod, size_tally, size_word]
  omega

/-- The encoded instruction runs on one finite multitape machine for arbitrary
address widths and arbitrary stage indices. -/
theorem on_tapes : PolyTreeMachine width send (fun q => send (reply q)) :=
  polyTreeMachine_of_BT (easy_reply.poly.on query_size) query_size

/-- Full padded spelling of the P192 binary address, in tape order. -/
def faceWord {k : ℕ} (x : Axon.Face k) : Word :=
  (Axon.alpha x).map (fun b => decide (b = 1))

@[simp] theorem length_faceWord {k : ℕ} (x : Axon.Face k) : (faceWord x).length = k := by
  rw [faceWord, List.length_map]
  exact List.length_ofFn

@[simp] theorem digit_faceWord {k : ℕ} (x : Axon.Face k) (j : Fin k) :
    (faceWord x)[j.val]'(by rw [length_faceWord]; exact j.isLt) = decide (x j = 1) := by
  simp only [faceWord, List.getElem_map]
  have len : (Axon.alpha x).length = k := List.length_ofFn
  have hj : j.val < (Axon.alpha x).length := by rw [len]; exact j.isLt
  have h : (Axon.alpha x)[j.val]'hj = (x j : Fin 2) := List.getElem_ofFn _
  rw [h]
  rfl

theorem reverse_faceWord {k : ℕ} (x : Axon.Face k) :
    (faceWord x).reverse = faceWord (Axon.refl_ x) := by
  simp [faceWord, Axon.alpha_refl]

private theorem value_map_bits (l : Adic.Raw 2) :
    value (l.map (fun b => decide (b = 1))) = Adic.code l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rcases b with ⟨n, hn⟩
    interval_cases n <;> simp [Adic.code, ih]

theorem value_faceWord {k : ℕ} (x : Axon.Face k) :
    value (faceWord x).reverse = Axon.bold x := by
  simpa [faceWord, List.map_reverse] using value_map_bits (Axon.alpha x).reverse

/-- Exact field layout of every valid stage query, including a zero numerator. -/
theorem reply_valid (w : Word) (j : ℕ) (hj : j < w.length) :
    reply (tally j, w) =
      (w.reverse, w.set j (!w[j]), tally (w.length - j),
        bif w[j] then (w.drop (j+1)).reverse else []) := by
  simp only [reply, cutLists, tally_length, List.drop_eq_getElem_cons hj, inspectTail,
    List.set_eq_take_append_cons_drop, hj, ↓reduceIte]
  have h : () :: ruler (w.drop (j+1)) = tally (w.length - j) := by
    apply List.ext_getElem
    · simp; omega
    · intros; rfl
  rw [h]

private theorem suffix_value (w : Word) (j : ℕ) :
    value (w.drop j).reverse = value w.reverse % 2 ^ (w.length - j) := by
  have h := congrArg (fun z : Word => value z.reverse) (List.take_append_drop j w)
  simp only [List.reverse_append, value_append, List.length_reverse, List.length_drop] at h
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  simpa using value_lt (w.drop j).reverse

variable {k : ℕ}

/-- A physical address in tape order, including its leading zeros. -/
def address (r : Fin (2 ^ k)) : Word := faceWord (rankBits r)

@[simp] theorem length_address (r : Fin (2^k)) : (address r).length = k :=
  length_faceWord _

theorem address_value (r : Fin (2^k)) : value (address r).reverse = r.val :=
  (value_faceWord _).trans (congrArg Fin.val (localV_rankBits r))

/-- Agreement with the padded binary word used by the P192 arithmetic routines. -/
theorem address_eq_phrase (r : Fin (2^k)) : address r = (phrase k r.val).reverse := by
  have h : (address r).reverse = phrase k r.val :=
    word_inject _ _ (by simp [phrase_length]) ((address_value r).trans (value_phrase r.isLt).symm)
  simpa only [List.reverse_reverse] using congrArg List.reverse h

theorem address_reverse (r : Fin (2^k)) :
    (address r).reverse = address (reverseRank r) := by
  simp only [address, reverseRank, rankBits_localV, reverse_faceWord]

private theorem address_set (i : Fin k) (r : Fin (2^k)) :
    (address r).set i.val (!(address r)[i.val]'(by simp)) = address (partnerRank i r) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have hjk : j < k := by simpa using hj'
  let a : Fin k := ⟨j,hjk⟩
  rw [List.getElem_set]
  have fixed (j : Fin k) (r : Fin (2^k)) : (address r)[j.val]'(by simp) = decide (rankBits r j = 1) :=
    digit_faceWord _ _
  change (if _ then !(address r)[i.val] else (address r)[a.val]) =
    (address (partnerRank i r))[a.val]
  simp only [fixed, rankBits_partner]
  by_cases h : a = i
  · have he : i.val = j := (congrArg Fin.val h).symm
    simp only [h, he, ↓reduceIte]
    rcases Net.Walsh.bit_value (rankBits r i) with h0 | h1 <;> simp [*]
  · have he : i.val ≠ j := fun eq => h (Fin.ext eq.symm)
    simp [he, h]

/-- All fields produced by the tape routine implement the integer-address
operations of the actual radix matrices. -/
theorem reply_rank (i : Fin k) (r : Fin (2^k)) :
    let p := reply (tally i.val, address r)
    p.1 = address (reverseRank r) ∧ p.2.1 = address (partnerRank i r) ∧
    p.2.2.1 = tally (k-i.val) ∧ value p.2.2.2 = twiddleNumerator i r := by
  dsimp only
  have hi : i.val < (address r).length := by simp
  rw [reply_valid _ _ hi]
  refine ⟨address_reverse _, address_set _ _, by rw [length_address], ?_⟩
  have hd := digit_faceWord (rankBits r) i
  change (address r)[i.val] = decide (rankBits r i = 1) at hd
  have bit (b : Bool) : decide ((if b then (1 : Net.Walsh.B) else 0) = 1) = b := by
    cases b <;> decide
  rw [hd.trans (bit _)]
  unfold twiddleNumerator
  by_cases h : r.val.testBit i.rev.val = true
  · simp only [h, ↓reduceIte, Bool.cond_true]
    rw [suffix_value, address_value, length_address]
    have he : k - (i.val + 1) = i.rev.val := by simp [Fin.rev]
    rw [he]
  · have hb : r.val.testBit i.rev.val = false := Bool.eq_false_iff.mpr h
    rw [ite_eq_right h, hb]
    rfl

/-- A single finite physical machine answers the queries for all valid ranks,
with time and visited cells polynomial in the width, including output. -/
theorem rank_queries_on_tapes :
    let X := (k : ℕ) × (Fin k × Fin (2^k))
    let q (x : X) : Query := (tally x.2.1.val, address x.2.2)
    PolyTreeMachine (fun x : X => x.1) (fun x => send (q x)) (fun x => send (reply (q x))) := by
  dsimp only
  have hw : Dom (fun x : (k : ℕ) × (Fin k × Fin (2^k)) => x.1)
      (fun x => size (tally x.2.1.val, address x.2.2)) := by
    refine ⟨1, 5, fun x => ?_⟩
    simp only [size_prod, size_tally, size_word, tally_length, length_address, pow_one]
    have hi := x.2.1.isLt
    omega
  exact polyTreeMachine_of_BT (easy_reply.poly.on hw) hw

/-- Releasing the linear stack program retains a linear bound in the width
of this local query, including the scan producing its physical output. -/
theorem rank_queries_linear_on_tapes :
    let X := (k : ℕ) × (Fin k × Fin (2^k))
    let q (x : X) : Query := (tally x.2.1.val, address x.2.2)
    LinearTreeMachine (fun x : X => x.1 + 1) (fun x => send (q x)) (fun x => send (reply (q x))) := by
  dsimp only
  apply linearTreeMachine_of_carries
  apply Carries.func (fun x => by exact_mod_cast Nat.le_add_left 1 x.1) _ _ easy_reply
  refine ⟨5, fun x => ?_⟩
  change ((size (tally x.2.1.val, address x.2.2) : ℕ) : ℝ) ≤ (5 : ℕ) * ((x.1 + 1 : ℕ) : ℝ)
  exact_mod_cast (show size (tally x.2.1.val, address x.2.2) ≤ 5 * (x.1 + 1) by
    simp only [size_prod, size_tally, size_word, tally_length, length_address]
    have hi := x.2.1.isLt
    omega)

end ShortFourier.RadixAddressTape

end NearSquareRoot
end Computability
end OAI
