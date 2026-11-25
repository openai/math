import OAI.Computability.BorderVNP.TeamTapeSortingRecords
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-!
# Extending logical probe words to physical sorting words

The phase bit used to distinguish the two records of a probe requires one more
address bit. Zero-extending the payload and access words to this physical
width preserves every step of the logical memory execution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamProbeEmit

open VPVNP BurstRAM TeamRecords

variable {w : ℕ}

/-- Extend a little-endian logical word by one zero high bit. -/
def widen (a : Word w) : Word (w + 1) :=
  ⟨a.val, a.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))⟩

/-- The enlarged word has exactly the old bits followed by a zero. -/
theorem wordBits_widen (a : Word w) : wordBits (widen a) = wordBits a ++ [false] := by
  apply TapeWord.eq_of_length_value
  · simp
  · simp [TapeWord.value_append, TapeWord.value_wordBits, TapeWord.value, widen]

/-- Widening preserves distinct word values. -/
theorem widen.injective : Function.Injective (widen (w := w)) :=
  fun _ _ h => Fin.ext (congrArg (fun a : Word (w + 1) => a.val) h)

/-- Change only the payload width of a four-word probe record. -/
def widenRecord (r : Record (Word w)) : Record (Word (w + 1)) :=
  ⟨r.address, r.tick, widen r.before, widen r.after⟩

/-- Zero-extend the optional write of an access. A read stays a read. -/
def widenAccess (e : Access (Word w)) : Access (Word (w + 1)) :=
  ⟨e.address, e.tick, e.write.map widen⟩

/-- Bounded logical addresses and ticks fit the physical pair, including its phase bit. -/
theorem probeFits_widenRecord (r : Record (Word w)) (ha : r.address < 2^w)
    (ht : r.tick < 2^w) : TeamTapeSorting.ProbeFits (widenRecord r) :=
  ⟨TeamTapeSorting.doubledAddress_fits ha,
   ht.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))⟩

private theorem widen_record (e : Access (Word w)) (a : Word w) :
    widenRecord (e.record a) = (widenAccess e).record (widen a) := by
  rcases e with ⟨_, _, write⟩
  cases write <;> rfl

/-- Widening all records agrees with executing the widened accesses from widened memory. -/
theorem widen_transcript (m : ℕ → Word w) (es : List (Access (Word w))) :
    (transcript m es).map widenRecord = transcript (widen ∘ m) (es.map widenAccess) := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, transcript, ih, widen_record, Function.comp_apply]
    congr 2
    rw [Function.comp_update]
    change Function.update (widen ∘ m) e.address (widen (e.record (m e.address)).after) =
      Function.update (widen ∘ m) e.address ((widenAccess e).record (widen (m e.address))).after
    rw [← widen_record]
    rfl

/-- All four fields of the original record are recovered uniquely from the widened record. -/
theorem widenRecord_injective : Function.Injective (widenRecord (w := w)) := by
  rintro ⟨a, t, b, c⟩ ⟨a', t', b', c'⟩ h
  obtain ⟨rfl, rfl, hb, hc⟩ := Record.mk.inj h
  obtain rfl := widen.injective hb
  obtain rfl := widen.injective hc
  rfl

/-- Widening the path and its guesses preserves the local instruction checks on every probe. -/
theorem matches_widen {es : List (Access (Word w))} {rs : List (Record (Word w))}
    (h : Matches es rs) : Matches (es.map widenAccess) (rs.map widenRecord) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    refine .cons ?_ ih
    exact (congrArg widenRecord h).trans (widen_record _ _)

/-- Access extension preserves the entire sequence of timestamp-address keys. -/
theorem timed_widen_iff (es : List (Access (Word w))) :
    Timed (es.map widenAccess) ↔ Timed es := by
  simp only [Timed, List.map_map]
  rfl

/-- From initially zero memory, validity of a full probe transcript is reflected by extension. -/
theorem widen_transcript_iff (rs : List (Record (Word w))) (es : List (Access (Word w))) :
    rs.map widenRecord = transcript (fun _ => 0) (es.map widenAccess) ↔
      rs = transcript (fun _ => 0) es := by
  have hzero : widen ∘ (fun _ : ℕ => (0 : Word w)) = fun _ => 0 := rfl
  rw [← hzero, ← widen_transcript]
  exact (List.map_injective_iff.mpr widenRecord_injective).eq_iff

end TeamProbeEmit

end BorderVNP
end Computability
end OAI
