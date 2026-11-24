import OAI.Computability.VPVNP.RAMTapeSortClock
import OAI.Computability.VPVNP.RAMTapeSortOneStage
import OAI.Computability.VPVNP.RAMTapeSortReplay
import OAI.Computability.VPVNP.RAMTapeSortStream

/-!
# Executable local sorting of the transcript records

The nested stage and offset loops run on the literal site stacks. For every
input bit vector, they consume exactly the suffix after the two successor
fields, materialize the selected block and retain every validity flag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortStages

open BurstRAM RAMSort RAMLayout RAMBoundary

/-- Registers for the phase and stride scheduler together with the registers used by each
sorting layer. -/
abbrev Port := SortSchedule.Port SortOneStage.Port

/-- Run the finite bitonic sorting schedule with the physical single-layer routine at every
stage. -/
def program : FiniteRoutine Port := SortSchedule.program SortOneStage.layer

variable {h d H w : ℕ}

/-- State between stages, with the actual remaining incident stream. -/
def data (v : Word d) (x : SortReplay.State h w) (stream : List Bool) : Stacks SortOneStage.Port :=
  SortOneStage.data v w h x.1 stream x.2

/-- Fold the site replay update over all bitonic stages on the combined row and site address
bits. -/
def result (raw : ℕ → Bool) (v : Word d) (x : SortReplay.State h w) : SortReplay.State h w :=
  (phases (h+d) (h+d) le_rfl).foldl (SortReplay.update raw v) x

private theorem flags_step (raw : ℕ → Bool) (v : Word d) (x : SortReplay.State h w) (s : Stage (h+d)) :
    (SortReplay.update raw v x s).2.length ≤ x.2.length + 2*2^h := by
  have bound (ls : List (List Bool)) (each : ∀ l ∈ ls, l.length ≤ 2) :
      ls.flatten.length ≤ 2*ls.length := by
    induction ls with
    | nil => rfl
    | cons y ys ih =>
      have hy := each y (by simp)
      have ht := ih (fun z hz => each z (List.mem_cons_of_mem _ hz))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_succ]
      omega
  let flags := SortLayerRows.checks s x.1 (SortReplay.fieldWords w raw s 0) (SortReplay.fieldWords w raw s 1)
  have each (i) : (flags i).length ≤ 2 := by
    simp only [flags, SortLayerRows.checks]; split <;> simp
  have hh := bound (List.ofFn flags).reverse (by
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hl)
    exact each i)
  simp only [List.length_reverse, List.length_ofFn] at hh
  change ((List.ofFn flags).reverse.flatten ++ x.2).length ≤ _
  rw [List.length_append]
  omega

theorem result_flags_length (raw : ℕ → Bool) (v : Word d) (x : SortReplay.State h w) :
    (result raw v x).2.length ≤ x.2.length + 2*2^h*((h+d+1).choose 2) := by
  have aux (ss : List (Stage (h+d))) (y : SortReplay.State h w) :
      (ss.foldl (SortReplay.update raw v) y).2.length ≤ y.2.length + 2*2^h*ss.length := by
    induction ss generalizing y with
    | nil => simp
    | cons s ss ih =>
      have hs := flags_step raw v y s
      have ht := ih (SortReplay.update raw v y s)
      simp only [List.foldl_cons, List.length_cons, Nat.mul_succ]
      omega
  simpa only [result, length_phases] using aux (phases (h+d) (h+d) le_rfl) x

/-- Every finite stage callback returns on every raw slot and field value.
Only the public stream lengths enter the clock. -/
theorem run_incident (hw : 2 ≤ w) (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k)
    (v : Word d) (x : SortReplay.State h w) :
    ∃ t ≤ ticks h d w, program.Runs t
      (SortSchedule.bank (data v x ((List.ofFn incident).drop (16*w))) (h+d) 0 0)
      (SortSchedule.bank (data v (result raw v x) []) 0 (h+d) 0) := by
  have one (y : SortReplay.State h w) (s : Stage (h+d)) (tail : List Bool) :
      ∃ t ≤ SortOneStage.budget h d w, SortOneStage.layer.Runs t
        (SortSchedule.bank (data v y (SortStream.bytes w raw s ++ tail)) (h+d-s.phase) s.phase s.stride)
        (SortSchedule.bank (data v (SortReplay.update raw v y s) tail) (h+d-s.phase) s.phase s.stride) := by
    have eq : SortOneStage.stream s (SortReplay.fieldWords w raw s 0) (SortReplay.fieldWords w raw s 1) tail =
        SortStream.bytes w raw s ++ tail := by
      by_cases hl : s.stride < h <;> simp [SortOneStage.stream, SortStream.bytes, hl, List.append_assoc]
    obtain ⟨t, ht, hr⟩ := SortOneStage.runs hw s v (h+d-s.phase) y.1
      (SortReplay.fieldWords w raw s 0) (SortReplay.fieldWords w raw s 1) tail y.2
    rw [eq] at hr
    exact ⟨t, ht, hr⟩
  have trace := SortSchedule.Visits.of_stream SortOneStage.layer (data v) (SortReplay.update raw v)
    (SortStream.bytes w raw) one (phases (h+d) (h+d) le_rfl) x []
  simp only [List.append_nil] at trace
  rw [SortStream.suffix hslots incident raw hraw]
  exact SortSchedule.runs_of_visits SortOneStage.layer trace

/-- The program returns the same decision as the word-level validator.
On every accepted input it returns the same parsed block, including the
final padded record used by the boundary pass. -/
theorem run_checked (hw : 2 ≤ w) (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k)
    (v : Word d) (x : SortReplay.State h w) (hcanon : SortReplay.CanonicalBlock hw x.1) :
    let ss := phases (h+d) (h+d) le_rfl
    let scan := scanStages hw raw v ss (SortReplay.decoded hw x.1)
    ∃ t ≤ ticks h d w, ∃ y : SortReplay.State h w, program.Runs t
      (SortSchedule.bank (data v x ((List.ofFn incident).drop (16*w))) (h+d) 0 0)
      (SortSchedule.bank (data v y []) 0 (h+d) 0) ∧
      y.2.all id = (x.2.all id && scan.ok) ∧
      (y.2.all id = true → SortReplay.CanonicalBlock hw y.1 ∧ SortReplay.decoded hw y.1 = scan.block) := by
  obtain ⟨t, ht, hr⟩ := run_incident hw hslots incident raw hraw v x
  exact ⟨t, ht, result raw v x, hr, SortReplay.fold_spec hw raw v _ x hcanon⟩


/-- On the actual live processor input, the final flags check every sorting
send and receive and the successful output is the typed validator's block. -/
theorem run_messages {e : ℕ} (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (b : SendArrays d (2^e) w) (v : Word d) (x : SortReplay.State (2+e) w)
    (hcanon : SortReplay.CanonicalBlock hw x.1) :
    let incident := fun j => (incidentEquiv d (2^e) w b).val (v, (offset d (2^e) w).symm j)
    let ss := phases ((2+e)+d) ((2+e)+d) le_rfl
    let mem := (unpackMessages (parseMessages hw hc b)).memory
    ∃ t ≤ ticks (2+e) d w, ∃ y : SortReplay.State (2+e) w, program.Runs t
      (SortSchedule.bank (data v x ((List.ofFn incident).drop (16*w))) ((2+e)+d) 0 0)
      (SortSchedule.bank (data v y []) 0 ((2+e)+d) 0) ∧
      y.2.length ≤ x.2.length + 2*2^(2+e)*(((2+e)+d+1).choose 2) ∧
      (y.2.all id = true ↔ x.2.all id = true ∧ SortCanonical hw hc b v ∧
        RAMSort.checks v ss (physicalFieldsEquiv.{0,0} (2+e) d _ mem.sortSends) (SortReplay.decoded hw x.1)) ∧
      (y.2.all id = true → (fun i => (parsedSlot hw (y.1 i)).record) =
        outputAt mem v (SortReplay.decoded hw x.1)) := by
  intro incident ss mem
  have hraw (k : Fin (width d (2^e) w)) : sortIncident b v k.val = incident k := readIncident_at _ k
  obtain ⟨t, ht, hr⟩ := run_incident hw (record_width e) incident (sortIncident b v) hraw v x
  exact ⟨t, ht, result (sortIncident b v) v x, hr, result_flags_length _ _ _, SortReplay.fold_messages hw hc b v x hcanon,
    SortReplay.fold_messages_output hw hc b v x hcanon⟩

end RAMTape.SortStages

end VPVNP
end Computability
end OAI
