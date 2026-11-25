import OAI.Computability.BorderVNP.CellSparseFactorCode
import OAI.Computability.BorderVNP.CellSparseSemantics

/-!
# Signed denotation of a compact cell directory

A scan of the factor occurrences preserves the incoming guard and sign. The selected gadget
positions are counted only by their identifiers. A separate range check rejects a position
outside the reported vector, even if every in-range count is correct.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

private abbrev readObservation (bank : ℕ → Bool) (o : Occurrence) :=
  o.factor.observe bank o.offset o.copy

private theorem map_read_some {α β : Type*} (read : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM read = some ys) : xs.map read = ys.map some := by
  induction xs generalizing ys with
  | nil => simpa using congrArg (Option.map (List.map some)) h
  | cons x xs ih =>
    cases hx : read x <;> cases hs : xs.mapM read <;> simp [hx, hs] at h
    subst ys
    simp [hx, ih _ hs]

private theorem all_present_iff {α β : Type*} (read : α → Option β) (xs : List α) :
    xs.all (fun x => (read x).isSome) = (xs.mapM read).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : read x <;> cases hs : xs.mapM read <;> simp [hx, hs, ih]

/-- Accumulate the presence and sign of all private factors, in directory order. -/
def Directory.factorFlags (D : Directory) (bank : ℕ → Bool) (f : Flags) : Flags :=
  D.occurrences.foldl (fun flags o => updateObservation (readObservation bank o) flags) f

private theorem fold_ok {α : Type*} (read : α → Option (Bool × Option ℕ)) (xs : List α) (f : Flags) :
    (xs.foldl (fun flags o => updateObservation (read o) flags) f).ok =
      (f.ok && xs.all (fun x => (read x).isSome)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.all_cons]
    exact Bool.and_assoc ..

/-- After an absent factor the success flag stays false, regardless of the incoming flags. -/
theorem factorFlags_none (D : Directory) (bank : ℕ → Bool) (f : Flags)
    (hobs : D.observations bank = none) : (D.factorFlags bank f).ok = false := by
  unfold Directory.factorFlags
  rw [fold_ok, all_present_iff]
  change (f.ok && (D.observations bank).isSome) = false
  simp [hobs]

private theorem fold_present (obs : List (Bool × Option ℕ)) (f : Flags) :
    (obs.map some).foldl (fun flags z => updateObservation z flags) f =
      ⟨f.ok, (obs.map Prod.fst).foldl Bool.xor f.minus⟩ := by
  induction obs generalizing f with
  | nil => rfl
  | cons z zs ih => simpa [updateObservation] using ih (updateObservation (some z) f)

/-- Successful reads retain the input guard and accumulate exactly the recorded sign bits. -/
theorem factorFlags_some (D : Directory) (bank : ℕ → Bool) (f : Flags)
    (obs : List (Bool × Option ℕ)) (hobs : D.observations bank = some obs) :
    D.factorFlags bank f = ⟨f.ok, (obs.map Prod.fst).foldl Bool.xor f.minus⟩ := by
  have hm := map_read_some (readObservation bank) D.occurrences obs hobs
  change D.occurrences.foldl _ f = _
  have h := fold_present obs f
  rw [← hm, List.foldl_map] at h
  exact h

/-- A missing gadget identifier contributes no count. A selected identifier must belong to the
reported vector, including when the finite-field entry at that position equals zero. -/
def selectedInRange (limit : ℕ) (bank : ℕ → Bool) (o : Occurrence) : Bool :=
  ((readObservation bank o).bind Prod.snd).all fun a => decide (a < limit)

private theorem selected_in_list (obs : List (Bool × Option ℕ)) (id : ℕ) :
    (obs.map some).countP (fun z => (z.bind Prod.snd) == some id) =
      (obs.filterMap Prod.snd).count id := by
  induction obs with
  | nil => rfl
  | cons z zs ih =>
    rcases z with ⟨b, o⟩
    cases o <;> simp [List.countP_cons, List.count_cons, ih]

/-- Count each selected gadget exactly once per occurrence, with repetitions retained. -/
theorem selected_count (D : Directory) (bank : ℕ → Bool) (obs : List (Bool × Option ℕ))
    (hobs : D.observations bank = some obs) (id : ℕ) :
    D.occurrences.countP (selected id bank) = (obs.filterMap Prod.snd).count id := by
  have h := selected_in_list obs id
  rw [← map_read_some (readObservation bank) D.occurrences obs hobs, List.countP_map] at h
  exact h

private theorem range_in_list (obs : List (Bool × Option ℕ)) (limit : ℕ) :
    (obs.map some).all (fun z => (z.bind Prod.snd).all (fun a => decide (a < limit))) = true ↔
      ∀ a ∈ obs.filterMap Prod.snd, a < limit := by
  induction obs with
  | nil => simp
  | cons z zs ih =>
    rcases z with ⟨b, o⟩
    cases o with
    | none => exact ih
    | some a =>
      change (decide (a < limit) && _) = true ↔ ∀ x ∈ a :: zs.filterMap Prod.snd, x < limit
      rw [Bool.and_eq_true, decide_eq_true_eq, ih, List.forall_mem_cons]

/-- Scanning all selected identifiers detects precisely the out-of-range observations. -/
theorem selectedInRange_iff (D : Directory) (bank : ℕ → Bool) (obs : List (Bool × Option ℕ))
    (hobs : D.observations bank = some obs) (limit : ℕ) :
    D.occurrences.all (selectedInRange limit bank) = true ↔
      ∀ a ∈ obs.filterMap Prod.snd, a < limit := by
  have h := range_in_list obs limit
  rw [← map_read_some (readObservation bank) D.occurrences obs hobs, List.all_map] at h
  exact h

/-- The full range and per-position equality tests are exactly the directory's count predicate. -/
theorem countsValid_iff (D : Directory) (bank : ℕ → Bool) (obs : List (Bool × Option ℕ))
    (hobs : D.observations bank = some obs) :
    countsValid bank D.reportedCounts obs ↔
      D.occurrences.all (selectedInRange D.reportedCounts.length bank) = true ∧
        ∀ id : Fin D.reportedCounts.length,
          D.occurrences.countP (selected id.val bank) = word bank D.reportedCounts[id] := by
  simp only [countsValid, selectedInRange_iff D bank obs hobs, selected_count D bank obs hobs]

/-- Combine any implementations of the record, count and range tests with the actual factor
sweep. The signed output is the incoming multiplicity times the exact directory weight. -/
theorem Directory.weight_eq_signedGuards (D : Directory) (bank : ℕ → Bool) (f : Flags)
    (wires counts : Bool)
    (hw : wires = true ↔ ∀ r ∈ D.records, r.Valid D.boxes bank)
    (hc : counts = true ↔ D.occurrences.all (selectedInRange D.reportedCounts.length bank) = true ∧
      ∀ id : Fin D.reportedCounts.length,
        D.occurrences.countP (selected id.val bank) = word bank D.reportedCounts[id]) :
    let g := D.factorFlags bank ⟨f.ok && wires, f.minus⟩
    TeamTape.haltWeight (g.ok && counts) g.minus =
      TeamTape.haltWeight f.ok f.minus * D.weight bank := by
  dsimp only
  cases hobs : D.observations bank with
  | none => simp [factorFlags_none D bank _ hobs, Directory.weight, hobs, TeamTape.haltWeight]
  | some obs =>
    have hpass : wires = true ∧ counts = true ↔
        (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs :=
      and_congr hw (hc.trans (countsValid_iff D bank obs hobs).symm)
    rw [factorFlags_some D bank _ obs hobs]
    have hxor (b : Bool) : (obs.map Prod.fst).foldl Bool.xor b =
        (b ^^ (obs.map Prod.fst).foldl Bool.xor false) := by
      simpa only [Bool.xor_false] using
        (List.foldl_assoc (op := Bool.xor) (l := obs.map Prod.fst) (a₁ := b) (a₂ := false))
    simp only [Directory.weight, hobs, ← hpass, hxor f.minus, TeamTape.haltWeight]
    cases f.ok <;> cases f.minus <;> cases wires <;> cases counts <;>
      cases (obs.map Prod.fst).foldl Bool.xor false <;> decide

end CellSparse

end BorderVNP
end Computability
end OAI
