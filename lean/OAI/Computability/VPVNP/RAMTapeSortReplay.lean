import OAI.Computability.VPVNP.RAMTapeSortReplayLayer
import OAI.Computability.VPVNP.RAMTapeSortReplayFields
import OAI.Computability.VPVNP.RAMSortScanMessages

/-! # Acceptance and output of the chronological physical sorting replay

A failed check is retained through every remaining stage, irrespective of
the later messages. On a successful prefix the physical block is canonical,
so the next stage starts from the exact block of the checked word-work scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open BurstRAM RAMSort RAMMemory RAMBoundary

variable {h d w : ℕ}

theorem fold_retains (raw : ℕ → Bool) (v : Word d) (ss : List (Stage (h+d))) (x : State h w)
    (hp : (ss.foldl (update raw v) x).2.all id = true) : x.2.all id = true := by
  induction ss generalizing x with
  | nil => exact hp
  | cons s ss ih => exact update_retains raw v x s (ih _ hp)

/-- Starting from any canonical local block and any saved check flags, both
sort scans have the same acceptance. When they pass, parsing the physical
output gives the replayed record array. -/
theorem fold_spec (hw : 2 ≤ w) (raw : ℕ → Bool) (v : Word d) (ss : List (Stage (h+d)))
    (x : State h w) (hcur : CanonicalBlock hw x.1) :
    let final := ss.foldl (update raw v) x
    let checked := scanStages hw raw v ss (decoded hw x.1)
    (final.2.all id = (x.2.all id && checked.ok)) ∧
      (final.2.all id = true → CanonicalBlock hw final.1 ∧ decoded hw final.1 = checked.block) := by
  induction ss generalizing x with
  | nil =>
    exact ⟨(Bool.and_true _).symm, fun _ => ⟨hcur,rfl⟩⟩
  | cons s ss ih =>
    let y := update raw v x s
    let layer := scanLayer hw raw s v (decoded hw x.1)
    have hy : y.2.all id = (x.2.all id && layer.ok) := update_flags hw raw v x s hcur
    change ((ss.foldl (update raw v) y).2.all id =
        (x.2.all id && (layer.ok && (scanStages hw raw v ss layer.block).ok))) ∧
      ((ss.foldl (update raw v) y).2.all id = true →
        CanonicalBlock hw (ss.foldl (update raw v) y).1 ∧
        decoded hw (ss.foldl (update raw v) y).1 = (scanStages hw raw v ss layer.block).block)
    rw [← Bool.and_assoc, ← hy]
    by_cases hgood : y.2.all id = true
    · obtain ⟨hcanon, hblock⟩ := update_output hw raw v x s hgood
      have ht := ih y hcanon
      change decoded hw y.1 = layer.block at hblock
      rw [← hblock]
      exact ht
    · have hfinal : (ss.foldl (update raw v) y).2.all id = false := by
        cases he : (ss.foldl (update raw v) y).2.all id
        · rfl
        · exact (hgood (fold_retains raw v ss y he)).elim
      have hold : y.2.all id = false := by cases he : y.2.all id <;> simp_all
      simp only [hold, hfinal, Bool.false_and, Bool.false_eq_true, false_implies, and_self]

variable {e : ℕ}

/-- For the actual incident messages, passing the physical rows checks both
canonicality and the typed send constraints at this site. -/
theorem fold_messages (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (b : RAMLayout.SendArrays d (2^e) w)
    (v : Word d) (x : State (2+e) w) (hcur : CanonicalBlock hw x.1) :
    let ss := phases ((2+e)+d) ((2+e)+d) le_rfl
    (ss.foldl (update (sortIncident b v) v) x).2.all id = true ↔
      x.2.all id = true ∧ SortCanonical hw hc b v ∧ RAMSort.checks v ss
        (physicalFieldsEquiv.{0,0} (2+e) d _ (unpackMessages (parseMessages hw hc b)).memory.sortSends)
        (decoded hw x.1) := by
  dsimp only
  rw [(fold_spec hw (sortIncident b v) v _ x hcur).1, Bool.and_eq_true, sortScan_messages hw hc b v]

/-- On passing physical messages the output supplied to the predecessor
test is the sorted record block of the typed distributed validator. -/
theorem fold_messages_output (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (b : RAMLayout.SendArrays d (2^e) w)
    (v : Word d) (x : State (2+e) w) (hcur : CanonicalBlock hw x.1) :
    let ss := phases ((2+e)+d) ((2+e)+d) le_rfl
    let final := ss.foldl (update (sortIncident b v) v) x
    final.2.all id = true →
      (fun i => (parsedSlot hw (final.1 i)).record) =
        outputAt (unpackMessages (parseMessages hw hc b)).memory v (decoded hw x.1) := by
  intro ss final hp
  have hblock := ((fold_spec hw (sortIncident b v) v ss x hcur).2 hp).2
  have hcan := ((fold_messages hw hc b v x hcur).mp hp).2.1
  exact (congrArg (fun f : Wires (2+e) (OrderedSlot (Word w)) => fun i => (f i).record) hblock).trans
    (sortScan_output hw hc b v (decoded hw x.1) hcan)

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
