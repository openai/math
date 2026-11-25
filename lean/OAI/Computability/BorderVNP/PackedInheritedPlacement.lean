import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Guard and observation semantics of final site relocation

The final directory points each reachable box reference into the common
one-copy list and adds the site's physical bit offset to each record. A
table whose factor wires are relative to its box keeps the same observation
at the new address. Both the guard and every accepted observation are
transported on arbitrary physical banks, before taking the private sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open scoped Classical

/-- Records for one site in the cell packet, with its original box table represented by a subinterval. -/
def Site.placedDirectory (s : Site) (merged : List (List Factor)) (off base : ℕ) : Directory :=
  ⟨merged,s.placedRows off base,[]⟩

/-- The observations accepted by the site's physical records before the cell combines count reports. -/
noncomputable def Site.placedObserve (s : Site) (merged : List (List Factor)) (off base : ℕ) (bank : ℕ → Bool) :
    Option (List (Bool × Option ℕ)) :=
  let d := s.placedDirectory merged off base
  if ∀ r ∈ d.records, r.Valid d.boxes bank then d.observations bank else none

private def shifted (s : Site) (off : ℕ) : Directory := ⟨s.boxes,s.rows.map (Record.shift · off),[]⟩

private theorem placed_eq (s : Site) (merged : List (List Factor)) (off base : ℕ) :
    s.placedDirectory merged off base = (shifted s off).rebaseBoxes merged base := by
  simp [Site.placedDirectory,Site.placedRows,shifted,Directory.rebaseBoxes,List.map_map,Function.comp_def]

private theorem shifted_refs (s : Site) (off : ℕ) (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length) :
    ∀ r ∈ (shifted s off).records, r.BoxRefFits (shifted s off).boxes.length := by
  intro r hr
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  have ok := fit t ht
  cases t <;> exact ok

/-- Physical guards are exactly the old record checks on the subbank at the given offset. -/
theorem Site.placed_valid (s : Site) (merged : List (List Factor)) (off base : ℕ)
    (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length) (span : base+s.boxes.length ≤ merged.length) (bank : ℕ → Bool) :
    (∀ r ∈ s.placedRows off base, r.Valid merged bank) ↔ ∀ r ∈ s.rows, r.Valid s.boxes (fun j => bank (off+j)) := by
  have hr := Directory.records_valid_rebaseBoxes (shifted s off) merged base bank (shifted_refs s off fit) span
  rw [←placed_eq] at hr
  exact hr.trans (by simp only [shifted,List.forall_mem_map,Record.valid_shift])

private def atOffset (off : ℕ) (o : Occurrence) : Occurrence := {o with offset := off+o.offset}

private theorem shifted_occurrences (s : Site) (off : ℕ) :
    (shifted s off).occurrences = s.directory.occurrences.map (atOffset off) := by
  simp only [shifted,Site.directory,Directory.occurrences,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro r _
  cases r with
  | box id base copies stride =>
    simp only [Record.shift,List.map_flatMap,List.map_map,Function.comp_def,atOffset,Nat.add_assoc]
  | _ => rfl

private theorem placed_occurrences (s : Site) (merged : List (List Factor)) (off base : ℕ)
    (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length)
    (get : ∀ i < s.boxes.length, merged.getD (base+i) [] = s.boxes.getD i []) :
    (s.placedDirectory merged off base).occurrences = s.directory.occurrences.map (atOffset off) := by
  rw [placed_eq,←Directory.blocks_visits,Directory.blocks_rebaseBoxes_of_getD _ _ _ (shifted_refs s off fit) get,
    Directory.blocks_visits,shifted_occurrences]

/-- Every reachable immutable factor is evaluated on its original relative wire list.
Unreferenced boxes need no shift condition. -/
theorem Site.placed_observations (s : Site) (merged : List (List Factor)) (off base : ℕ)
    (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length)
    (get : ∀ i < s.boxes.length, merged.getD (base+i) [] = s.boxes.getD i [])
    (fixed : ∀ o ∈ s.directory.occurrences, o.factor.shift off = o.factor) (bank : ℕ → Bool) :
    (s.placedDirectory merged off base).observations bank = s.directory.observations (fun j => bank (off+j)) := by
  unfold Directory.observations
  rw [placed_occurrences s merged off base fit get,List.mapM_map]
  have go (xs : List Occurrence) (h : ∀ o ∈ xs, o.factor.shift off = o.factor) :
      xs.mapM (fun o => o.factor.observe bank (off+o.offset) o.copy) =
      xs.mapM (fun o => o.factor.observe (fun j => bank (off+j)) o.offset o.copy) := by
    induction xs with
    | nil => rfl
    | cons o xs ih =>
      have hr := o.factor.observe_shift off o.offset o.copy bank
      rw [h o List.mem_cons_self] at hr
      simp only [List.mapM_cons,hr,ih (fun x hx => h x (List.mem_cons_of_mem o hx))]
      rfl
  exact go _ fixed

/-- Final relocation preserves rejection, signs, gadget IDs, and their order for every bank. -/
theorem Site.placed_observe (s : Site) (merged : List (List Factor)) (off base : ℕ)
    (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length) (span : base+s.boxes.length ≤ merged.length)
    (get : ∀ i < s.boxes.length, merged.getD (base+i) [] = s.boxes.getD i [])
    (fixed : ∀ o ∈ s.directory.occurrences, o.factor.shift off = o.factor) (bank : ℕ → Bool) :
    s.placedObserve merged off base bank = s.observe (fun j => bank (off+j)) := by
  unfold Site.placedObserve Site.observe
  have guards := s.placed_valid merged off base fit span bank
  change (∀ r ∈ (s.placedDirectory merged off base).records, r.Valid (s.placedDirectory merged off base).boxes bank) ↔ _ at guards
  simp only [guards,s.placed_observations merged off base fit get fixed bank]

/-- If the site's finite physical extent contains its own work and input words, summing
the placed observations over its private work gives its intrinsic table value. -/
theorem Site.placed_value {R : Type*} [AddCommMonoid R] (s : Site) (locality : s.Local)
    (merged : List (List Factor)) (off base : ℕ) (fit : ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length)
    (span : base+s.boxes.length ≤ merged.length) (get : ∀ i < s.boxes.length, merged.getD (base+i) [] = s.boxes.getD i [])
    (fixed : ∀ o ∈ s.directory.occurrences, o.factor.shift off = o.factor) (weight : List (Bool × Option ℕ) → R)
    (input : Fin s.incoming → Bool) (bank : (Fin s.work → Bool) → ℕ → Bool)
    (extent : ∀ work j, j < s.size → bank work (off+j) = bits work input j) :
    (∑ work, (s.placedObserve merged off base (bank work)).elim 0 weight) = s.value weight input := by
  unfold Site.value
  apply Finset.sum_congr rfl
  intro work _
  rw [s.placed_observe merged off base fit span get fixed]
  exact congrArg (Option.elim · 0 weight) (locality _ _ (extent work))

end Packing.Inherited

end BorderVNP
end Computability
end OAI
