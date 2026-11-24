import OAI.Computability.VPVNP.RAMTranscript
import OAI.Computability.VPVNP.RAMFinite

/-!
# Materializing the site's initial sorting block

The site reserves space for four slots per unit of bucket capacity and writes
its header and probe records there in chronological order. Every event is
visited once. The write pointer supplies the probe count of a completed call.
Unwritten slots read as padding.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMSort

variable {w : ℕ}

private abbrev Buffer (w : ℕ) := Array (Record (Word w))

/-- Append five words on a probe, leaving private instructions and choices out
of the sorting block. The work includes the event test and loop control. -/
private def appendEvents (start : ℕ) : ℕ → List (Event w) → Buffer w → Buffer w × ℕ
  | _, [], buf => (buf, 1)
  | j, .read a x :: es, buf =>
    let next := appendEvents start (j + 1) es (buf.push ⟨.read, a.val, x, start, j⟩)
    (next.1, 12 + next.2)
  | j, .write a x :: es, buf =>
    let next := appendEvents start (j + 1) es (buf.push ⟨.write, a.val, x, start, j⟩)
    (next.1, 12 + next.2)
  | j, _ :: es, buf =>
    let next := appendEvents start j es buf
    (next.1, 4 + next.2)

private theorem appendEvents_data (start j : ℕ) (es : List (Event w)) (buf : Buffer w) :
    (appendEvents start j es buf).1.toList = buf.toList ++ eventRecords start j es := by
  induction es generalizing j buf with
  | nil => simp [appendEvents, eventRecords]
  | cons e es ih => cases e <;> simp [appendEvents, eventRecords, ih, List.append_assoc]

private theorem appendEvents_work (start j : ℕ) (es : List (Event w)) (buf : Buffer w) :
    (appendEvents start j es buf).2 ≤ 12 * es.length + 1 := by
  induction es generalizing j buf with
  | nil => simp [appendEvents]
  | cons e es ih =>
    cases e <;> simp only [appendEvents, List.length_cons, Nat.mul_add] <;>
      apply le_trans (Nat.add_le_add_left (ih _ _) _) <;> omega

private def appendCalls : ℕ → List (Report w) → Buffer w → Buffer w × ℕ
  | _, [], buf => (buf, 1)
  | start, r :: rs, buf =>
    let step := appendEvents start 0 r.events buf
    let next := appendCalls (start + (1 + (step.1.size - buf.size))) rs step.1
    (next.1, 8 + step.2 + next.2)

private theorem appendCalls_data (start : ℕ) (rs : List (Report w)) (buf : Buffer w) :
    (appendCalls start rs buf).1.toList = buf.toList ++ probeRecords start rs := by
  induction rs generalizing start buf with
  | nil => simp [appendCalls, probeRecords]
  | cons r rs ih =>
    have h := congrArg List.length (appendEvents_data start 0 r.events buf)
    simp only [Array.length_toList, List.length_append, length_eventRecords] at h
    simp [appendCalls, ih, appendEvents_data, h, Report.probes, probeRecords, List.append_assoc]

private theorem appendCalls_work (start fuel : ℕ) (rs : List (Report w)) (buf : Buffer w)
    (hs : ∀ r ∈ rs, r.events.length < fuel) :
    (appendCalls start rs buf).2 ≤ rs.length * (12 * fuel + 9) + 1 := by
  induction rs generalizing start buf with
  | nil => simp [appendCalls]
  | cons r rs ih =>
    simp only [List.forall_mem_cons] at hs
    have he := appendEvents_work start 0 r.events buf
    simp only [appendCalls, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hr := ih (start + (1 + ((appendEvents start 0 r.events buf).1.size - buf.size)))
      (appendEvents start 0 r.events buf).1 hs.2
    omega

/-- The array view uses a single constant-time indexed lookup. Missing slots
have the same zero-padding meaning as the full length-`4H` representation. -/
def recordBuffer (e v : ℕ) (header : Word w) (start : ℕ) (rs : List (Report w)) :
    Wires (2 + e) (OrderedSlot (Word w)) × ℕ :=
  let init := (Array.emptyWithCapacity (4 * 2 ^ e)).push (initRecord (fun _ => header) v)
  let result := appendCalls start rs init
  (fun j => ⟨result.1[j.val]?⟩, 16 + result.2)

private theorem get_padded {α : Type*} (l : List α) (k j : ℕ) :
    (l.map some ++ List.replicate k none)[j]?.getD none = l[j]? := by
  by_cases hj : j < l.length
  · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map,
      List.getElem?_eq_getElem hj]
    rfl
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hj),
      List.getElem?_eq_none (Nat.le_of_not_gt hj)]
    by_cases hk : j - l.length < k <;> simp [hk]

theorem recordBuffer_data (e v : ℕ) (header : ℕ → Word w) (start : ℕ) (rs : List (Report w)) :
    (recordBuffer e v (header v) start rs).1 = localRecords header e v start rs := by
  funext j
  apply congrArg OrderedSlot.mk
  unfold siteRecordBlock
  rw [← Array.getElem?_toList, appendCalls_data, get_padded]
  rfl

/-- On all report lists returned by the site, the single-pass collection takes
at most a constant number of word operations per simulated instruction. -/
theorem recordBuffer_work {C : Type*} {P : Program w C} {fuel S e v : ℕ}
    {input : Cut w} {rs : List (Report w)} (header : Word w)
    (hs : SiteRun P fuel S (2 ^ e) v input rs) :
    (recordBuffer e v header input.cost rs).2 ≤ 17 + (2 * 2 ^ e) * (12 * fuel + 9) := by
  obtain ⟨hl, he⟩ := boundedReports_of_localSegment hs.calls (hs.cost_lt (Nat.two_pow_pos e)).le
  have h := appendCalls_work input.cost fuel rs
    ((Array.emptyWithCapacity (4 * 2 ^ e)).push (initRecord (fun _ => header) v)) he
  have hr := Nat.mul_le_mul_right (12 * fuel + 9) hl
  dsimp only [recordBuffer]
  omega

end BurstRAM

end VPVNP
end Computability
end OAI
