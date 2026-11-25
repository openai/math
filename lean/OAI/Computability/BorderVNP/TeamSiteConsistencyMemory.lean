import OAI.Computability.BorderVNP.TeamSiteConsistencyRows
import OAI.Computability.BorderVNP.TeamContractionWireChecks

/-! # Native memory correctness of the actual per-site sorting rows

The full bit-level input is concatenated once in real-processor order. Initial writes
use time zero, and all later guesses are checked against that same mutable memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape RAMSerialization TeamRAM TeamEventRecords
open BurstRAM (Word Memory)
open TeamProbeEmit (widen widenRecord widenAccess)
open TeamContraction.Wires TeamTapeSorting TeamTapeInputRoute.Verify
variable {w r k e : ℕ}

/-- All input words in chronological address order, including each processor's program
prefix and exterior pins. -/
def inputMemory (w : ℕ) (input : Fin r → List Bool) : Memory w :=
  let bits := (List.ofFn input).flatten
  RAMMemory.initialMemory bits.length (TeamTapeInputEmit.headerWord w bits)

/-- Actual native access sequence, zero-extended onto the doubled-phase sorter. -/
def actions (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) :
    List (TeamRecords.Access (Word (w+1))) :=
  let bits := (List.ofFn input).flatten
  (TeamTranscript.accesses Event.action bits.length (TeamTapeInputEmit.headerWord w bits)
    (List.ofFn blocks).flatten).map widenAccess

private theorem widen_probes (hw : 0 < w) (a : ℕ) (bits : List Bool) :
    (TeamTapeInputEmit.probes w a bits).map widenRecord = TeamTapeInputEmit.probes (w+1) a bits := by
  have hh : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
  have one (b : Bool) : widen (TeamTapeInputEmit.word w b.toNat) = TeamTapeInputEmit.word (w+1) b.toNat := by
    apply Fin.ext
    change b.toNat % 2^w = b.toNat % 2^(w+1)
    rw [Nat.mod_eq_of_lt (by have := b.toNat_le; omega), Nat.mod_eq_of_lt (by have := b.toNat_le; rw [pow_succ]; omega)]
  induction bits generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [TeamTapeInputEmit.probes,List.map_cons,ih]
    exact congrArg (· :: TeamTapeInputEmit.probes (w+1) (a+1) bs)
      (show widenRecord (TeamTapeInputEmit.probe w a b) = TeamTapeInputEmit.probe (w+1) a b from
        by exact congrArg (TeamRecords.Record.mk a 0 (0 : Word (w+1))) (one b))

private theorem chronological (hw : 0 < w) (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) :
    chronology input blocks =
      ((TeamTapeInputEmit.probes w 0 (List.ofFn input).flatten) ++ historyFields 1 (List.ofFn blocks).flatten).map widenRecord := by
  simp only [chronology,List.map_append,widen_probes hw]

/-- Every emitted field is an admissible claim for its own native access. The times of
the claims are exactly the ordered logical times, including all time-zero writes. -/
theorem chronology_spec {S : Type*} (hw : 0 < w) (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    {P : S → Instr w S} {s : S} (loc : Local P s (List.ofFn blocks).flatten) :
    TeamRecords.Matches (actions input blocks) (chronology input blocks) ∧ TeamRecords.Timed (actions input blocks) := by
  let bits := (List.ofFn input).flatten
  let es := (List.ofFn blocks).flatten
  let h := TeamTapeInputEmit.headerWord w bits
  rw [chronological hw, actions]
  refine ⟨TeamProbeEmit.matches_widen ?_,(TeamProbeEmit.timed_widen_iff _).mpr (TeamTranscript.accesses_timed ..)⟩
  change TeamRecords.Matches (TeamRecords.initialization bits.length h ++ TeamTranscript.probes Event.action 1 es) _
  rw [TeamTapeInputEmit.probes_initialization]
  exact List.rel_append (TeamRecords.matches_transcript ..) (history_spec 1 es (arity_of_local loc)).1

/-- A full widened transcript agrees with the proposed physical fields exactly when
the register path used the actual RAM words initialized by the real raw input. -/
theorem chronology_eq_transcript_iff {S : Type*} (hw : 0 < w) (input : Fin r → List Bool)
    (blocks : Fin r → List (Event w)) {P : S → Instr w S} {s : S}
    (loc : Local P s (List.ofFn blocks).flatten) :
    chronology input blocks = TeamRecords.transcript (fun _ => 0) (actions input blocks) ↔
      Correct (inputMemory w input) (List.ofFn blocks).flatten := by
  let bits := (List.ofFn input).flatten
  let es := (List.ofFn blocks).flatten
  let h := TeamTapeInputEmit.headerWord w bits
  rw [chronological hw,actions,TeamProbeEmit.widen_transcript_iff,TeamTranscript.accesses,
    TeamTapeInputEmit.probes_initialization,TeamRecords.transcript_initialization]
  have start := TeamRecords.transcript_initialization bits.length h []
  simp only [List.append_nil,TeamRecords.transcript] at start
  rw [start,List.append_right_inj]
  exact history_eq_transcript_iff loc _ _

/-- The complete interior bit assignment is unique for each locally valid path on
true memory and a fixed handoff chain. This uses the actual initialized and appended
physical rows, and all virtual sort blocks are checked on their real owners. -/
theorem unique_links_iff_native {S : Type*} (hr : 0 < r) (hw : 2 ≤ w+1)
    (hc : 2^(Nat.clog 2 r)*2^e < 2^(w+1)) (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (frames : Fin (r-1) → TeamTapeHandoff.Frame w k)
    (hi : ∀ j, 2*(TeamTapeInputEmit.rowStart input j + (input j).length) ≤ 2^(w+1))
    (hf : ∀ j, ∀ z ∈ rowFields input blocks j, ProbeFits z)
    (hfit : ∀ j, 2*(rowFields input blocks j).length ≤ 4*2^e)
    {P : S → Instr w S} {s : S} (loc : Local P s (List.ofFn blocks).flatten) :
    let x := rowInput e (padRows (realRows input blocks))
    (∃! links : Edge r k w e (w+1) → Bool,
      (∀ j, List.ofFn ((edgeEquiv links).1 j) = (frames j).bits) ∧
        ∀ j, ownerValid hw hc (edgeEquiv links).2 x (primary j) (secondary j)) ↔
      execute P s (inputMemory w input) ((List.ofFn blocks).flatten.map Event.choices) = some (List.ofFn blocks).flatten := by
  have positive : 0 < w := by omega
  have he : realRows input blocks = fun j => packRow (rowFields input blocks j) (hf j) := by
    funext j; exact realRows_eq_packRow _ _ _ (hi j) (hf j)
  obtain ⟨hm,ht⟩ := chronology_spec positive input blocks loc
  dsimp only
  have h := unique_interior_iff hr hw hc frames _ hf hfit hm ht (chronology_perm input blocks)
  dsimp only at h
  rw [he,h,
    chronology_eq_transcript_iff positive input blocks loc,execute_iff]
  exact ⟨fun correct => ⟨loc,correct,rfl⟩, fun h => h.2.1⟩

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
