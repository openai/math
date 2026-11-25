import OAI.Computability.MultitapeWeakETH.FrameDecoding
import OAI.Computability.MultitapeWeakETH.ReaderEnumeration
import OAI.Computability.VPVNP.PairTerminalGatherGeometry

/-! # Enumerating all shared payloads of a terminal graph on the decision tapes -/

namespace OAI.Computability.MultitapeWeakETH.TerminalWords

open IntegerMultiplication Code VPVNP Compression PairSimulation
open scoped Classical
open private zeros zeros_poly zeros_iff from OAI.Computability.MultitapeWeakETH.FrameDecoding

/-- The declared wire bits occupy the prefix; there is a unique valid suffix
at each candidate length. A short candidate is rejected even if all its bits are zero. -/
def unpack (q : Tally × Bits.Word) : Option Bits.Word :=
  let parts := cutLists q
  bif Iter.small q.swap then none
  else bif zeros parts.2 then some parts.1 else none

theorem unpack_poly : Poly unpack := by
  have split : Easy (cutLists (X:=Bool)) := easy_cut Easy.identity
  have ok := split.sndCompose.poly.compose zeros_poly
  have done := Poly.choose ok (split.fstCompose.compose Easy.some).poly (Code.Poly.const none)
  exact Poly.choose (Easy.exchange.compose Iter.small_easy).poly (Code.Poly.const none) done

theorem unpack_iff (n : ℕ) (bits row : Bits.Word) : unpack (tally n,bits) = some row ↔
    row.length=n ∧ bits=row++List.replicate (bits.length-n) false := by
  simp only [unpack,Iter.small,Prod.swap,cutLists,tally_length]
  by_cases h : bits.length < n
  · simp [h]
    intro len eq
    have := congrArg List.length eq
    simp [len] at this
    omega
  · simp only [decide_eq_false h,Bool.cond_false]
    cases z : zeros (bits.drop n) with
    | false =>
      change none = some row ↔ _
      simp only [reduceCtorEq,false_iff,not_and]
      intro len eq
      have all : zeros (bits.drop n) = true := (zeros_iff _).mpr (by
        conv_lhs => rw [eq,← len,List.drop_left]
        simp [List.length_drop,len])
      simp [z] at all
    | true =>
      change some (bits.take n) = some row ↔ _
      simp only [Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨by simp [Nat.min_eq_left (by omega : n ≤ bits.length)],?_⟩
        have tail := (zeros_iff _).mp z
        rw [List.length_drop] at tail
        exact (List.take_append_drop n bits).symm.trans (congrArg _ tail)
      · rintro ⟨len,eq⟩
        conv_lhs => rw [eq,← len,List.take_left]

private theorem unpack_decode (n : ℕ) (bits : Bits.Word) :
    unpack (tally n,bits) = (ReaderEnumeration.decode (LocalHistory.bitField n) bits).map List.ofFn := by
  cases h : ReaderEnumeration.decode (LocalHistory.bitField n) bits with
  | some f =>
    apply (unpack_iff ..).mpr
    have d := (ReaderEnumeration.decode_iff _).mp h
    simpa [ReaderEnumeration.padded,PrivateFields.bitField_encode] using d.2
  | none =>
    cases e : unpack (tally n,bits) with
    | none => rfl
    | some row =>
      obtain ⟨len,eq⟩ := (unpack_iff ..).mp e
      let f (i : Fin n) := row[i.val]'(len ▸ i.isLt)
      have rows : List.ofFn f = row := by apply List.ext_getElem <;> simp [f,len]
      have read : ReaderEnumeration.decode (LocalHistory.bitField n) bits = some f := by
        apply (ReaderEnumeration.decode_iff _).mpr
        rw [LocalHistory.bitField_length]
        refine ⟨?_,?_⟩
        · have l := congrArg List.length eq
          simp [len] at l
          omega
        · simpa [ReaderEnumeration.padded,PrivateFields.bitField_encode,rows,len] using eq
      simp [h] at read

/-- A fixed-depth Boolean search yields each shared assignment once for
arbitrary widths, including zero-width edges and empty terminal graphs. -/
theorem payload_sum {a g : ℕ} (X : State a g) {V : Type} [AddCommMonoid V]
    (L : ℕ) (fits : X.totalWidth ≤ L) (value : Bits.Word → V) :
    ReaderEnumeration.treeSum (fun bits => (unpack (tally X.totalWidth,bits)).elim 0 value) L [] =
      ∑ h : (e : X.network.Edge) → X.network.Payload e,
        value (List.ofFn ((TerminalGatherGeometry.payload X).symm h)) := by
  rw [← TerminalPrefix.width_sum X,← (TerminalGatherGeometry.payload X).sum_comp]
  simp only [Equiv.symm_apply_apply]
  let t := ∑ i, TerminalPrefix.width X i
  let parser := LocalHistory.bitField t
  have term (bits : Bits.Word) : (unpack (tally t,bits)).elim 0 value =
      (ReaderEnumeration.decode parser bits).elim 0 (fun f => value (List.ofFn f)) := by
    rw [unpack_decode]
    cases ReaderEnumeration.decode parser bits <;> rfl
  exact (congrArg (fun F => ReaderEnumeration.treeSum F L []) (funext term)).trans
    (ReaderEnumeration.sum_decode parser L (fun f => by
      simpa [parser,t,TerminalPrefix.width_sum] using fits) _)

end OAI.Computability.MultitapeWeakETH.TerminalWords
