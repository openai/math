import OAI.Computability.VPVNP.LiveConfigGatherImage

/-!
# The complete native configuration-gather scan

The persistent cursor visits every destination exactly once. Each successful
completion consists of one empty choice list per word. The individual reports
identify the actual writes and permit replay on the live group's external memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveConfigGather

open BurstRAM
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Instantiate the gathering table on the live public operands to obtain its executable RAM
program. -/
abbrev machine (pub : Pub → Word w) := (table.instantiate w pub).program

/-- The gather report for one indexed word of a configuration, using that word's index as the
persistent cursor. -/
def wordReport (pub : Pub → Word w) (words : Fin k → Word w) (i : Fin k) :=
  report pub (i.val : Word w) (fun _ => 0) (words i)

private def cursor (w k i : ℕ) : Option (Word w) :=
  if i = k then none else some (i : Word w)

private theorem report_result (pub : Pub → Word w) (hk : (pub 3).val = k) (words : Fin k → Word w)
    (i : Fin k) : (wordReport pub words i).result = cursor w k (i.val + 1) := by
  have cap : k < 2 ^ w := hk ▸ (pub 3).isLt
  have hl : i.val + 1 < 2 ^ w := (Nat.succ_le_of_lt i.isLt).trans_lt cap
  have h : (i.val : Word w) + 1 = ((i.val+1 : ℕ) : Word w) := by simp
  have he : ((i.val+1 : ℕ) : Word w) = pub 3 ↔ i.val + 1 = k := by
    rw [Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hl, hk]
  simp only [wordReport, report, cursor, h, he]

private theorem ordered_run (pub : Pub → Word w) (words : Fin k → Word w) (hw : 2 ≤ w)
    (hp : (pub 2).val = w) (hk : (pub 3).val = k) {fuel : ℕ} (hf : 8*w+20 ≤ fuel)
    (inv : Memory w → Prop)
    (img : ∀ m, inv m → ∀ i : Fin k, BitImage m (pub 0 + (i.val : Word w) * pub 2) (words i))
    (pres : ∀ m, inv m → ∀ i : Fin k, inv (writeMemory m (pub 1 + (i.val : Word w)) (words i)))
    (cells : List (Fin k)) (start : ℕ) (hend : start + cells.length = k)
    (ord : ∀ j (hj : j < cells.length), cells[j].val = start + j)
    (m : Memory w) (hm : inv m) (bs : List (List Bool)) (reps : List (Report w)) :
    (runSegment (machine pub) fuel (cursor w k start) m bs = some reps ∧
      endState (cursor w k start) reps = none) ↔
      bs = List.replicate cells.length [] ∧ reps = cells.map (wordReport pub words) := by
  induction cells generalizing start m bs reps with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at hend
    subst start
    cases bs <;> cases reps <;> simp [cursor, runSegment, endState]
  | cons i cells ih =>
    have hi : i.val = start := by
      have he := ord 0 (by simp)
      change i.val = start + 0 at he
      exact he
    subst start
    have htail : i.val + 1 + cells.length = k := by simp only [List.length_cons] at hend; omega
    have hseq (j : ℕ) (hj : j < cells.length) : cells[j].val = i.val + 1 + j := by
      have he := ord (j+1) (by simpa using hj)
      change cells[j].val = i.val + (j+1) at he
      omega
    have hlt : (i.val : Word w) < pub 3 := by
      rw [Fin.lt_def, Fin.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans (hk ▸ (pub 3).isLt)), hk]
      exact i.isLt
    have hc : cursor w k i.val = some (i.val : Word w) := by simp [cursor, i.isLt.ne]
    cases bs with
    | nil => cases reps <;> simp [hc, runSegment, endState, List.replicate_succ]
    | cons b bs =>
      have run := gather_call_at_fuel pub (i.val : Word w) (fun _ => 0) m hw hp hlt (words i) (img m hm i)
        (fun _ => 0) b hf
      change execute (machine pub) fuel ((machine pub).start (i.val : Word w)) m b =
        (if b.isEmpty then some (wordReport pub words i) else none) at run
      rw [hc, runSegment, run]
      cases b with
      | cons bit more => simp [List.replicate_succ]
      | nil =>
        let rep := wordReport pub words i
        have hn := report_result pub hk words i
        have hmem : after m rep.events = writeMemory m (pub 1 + (i.val : Word w)) (words i) := report_memory ..
        simp only [List.isEmpty_nil, ite_true, List.length_cons, List.replicate_succ, List.map_cons,
          List.cons.injEq, true_and, hn, Option.map_eq_some_iff]
        cases reps with
        | nil => simp
        | cons z zs =>
          simp only [List.cons.injEq, endState]
          by_cases hz : rep = z
          · subst z
            simpa [rep, hn, hmem] using
              ih (i.val+1) htail hseq _ (pres m hm i) bs zs
          · simp [rep] at hz
            simp [hz, Ne.symm hz]

/-- Exact choices and reports of a complete execution, for an array of
words whose source bits survive the earlier writes. -/
theorem run_words (pub : Pub → Word w) (words : Fin k → Word w) (hw : 2 ≤ w) (hp : (pub 2).val = w)
    (hk : (pub 3).val = k) (hpos : 0 < k) {fuel : ℕ} (hf : 8*w+20 ≤ fuel) (inv : Memory w → Prop)
    (img : ∀ m, inv m → ∀ i : Fin k, BitImage m (pub 0 + (i.val : Word w) * pub 2) (words i))
    (pres : ∀ m, inv m → ∀ i : Fin k, inv (writeMemory m (pub 1 + (i.val : Word w)) (words i)))
    (m : Memory w) (hm : inv m) (bs : List (List Bool)) (reps : List (Report w)) :
    (runSegment (machine pub) fuel (some 0) m bs = some reps ∧ endState (some 0) reps = none) ↔
      bs = List.replicate k [] ∧ reps = (List.finRange k).map (wordReport pub words) := by
  simpa [cursor, hpos.ne] using ordered_run pub words hw hp hk hf inv img pres (List.finRange k) 0
    (by simp) (by intro j hj; simp) m hm bs reps

/-- Exact native completion and memory replay for the unpacked live cut:
the stage admits one deterministic transcript and installs every decoded
word in the destination bank. -/
theorem run_array (pub : Pub → Word w) (bits : Fin (k*w) → Bool) (hw : 2 ≤ w)
    (hp : (pub 2).val = w) (hk : (pub 3).val = k) (hpos : 0 < k) {fuel : ℕ}
    (hf : 8*w+20 ≤ fuel) (srcFit : (pub 0).val + k*w ≤ 2^w) (destFit : (pub 1).val + k ≤ 2^w)
    (hsep : (pub 0).val + k*w ≤ (pub 1).val ∨ (pub 1).val + k ≤ (pub 0).val)
    (m : Memory w) (hm : ArrayBitImage m (pub 0) bits)
    (bs : List (List Bool)) (reps : List (Report w)) (out : Memory w) :
    (runSegment (machine pub) fuel (some 0) m bs = some reps ∧ endState (some 0) reps = none ∧
      after m (eventLog reps) = out) ↔
      bs = List.replicate k [] ∧
        reps = (List.finRange k).map (wordReport pub ((RAMSerialization.arrayBits k w).symm bits)) ∧
        out = gathered (pub 1) destFit bits m := by
  let words := (RAMSerialization.arrayBits k w).symm bits
  have hr := run_words pub words hw hp hk hpos hf (fun u => ArrayBitImage u (pub 0) bits)
    (fun _ h i => bitImage_word h srcFit hp i)
    (fun _ h i => h.after_write destFit hsep i (words i)) m hm bs reps
  have hm' : after m (eventLog ((List.finRange k).map (wordReport pub words))) =
      gathered (pub 1) destFit bits m := replay_reports pub destFit _ words (List.finRange k) m
  constructor
  · rintro ⟨run, he, hmem⟩
    obtain ⟨hbs, hrep⟩ := hr.mp ⟨run, he⟩
    exact ⟨hbs, hrep, hmem.symm.trans (hrep ▸ hm')⟩
  · rintro ⟨hbs, hrep, rfl⟩
    obtain ⟨run, he⟩ := hr.mpr ⟨hbs, hrep⟩
    exact ⟨run, he, hrep ▸ hm'⟩

end LiveConfigGather

end VPVNP
end Computability
end OAI
