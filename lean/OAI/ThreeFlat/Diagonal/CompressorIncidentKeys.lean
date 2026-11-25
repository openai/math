import OAI.ThreeFlat.Diagonal.CompressorNodeIncident

namespace OAI
/-! # First incident records at distinct evaluated keys -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

open Computability.VPVNP.BurstRAM

variable {W : ℕ} (V : F → Word W)

/-- Retain the first hit at each nonzero key outside the initial seen list. -/
def selected (seen : List (Word W)) : List Hit → List Hit
  | [] => []
  | a :: xs =>
    let tail := selected (V a.key :: seen) xs
    if V a.key ≠ 0 ∧ V a.key ∉ seen then a :: tail else tail

theorem selected_sublist (seen : List (Word W)) (xs : List Hit) :
    (selected V seen xs).Sublist xs := by
  induction xs generalizing seen with
  | nil => exact .refl _
  | cons a xs ih =>
    simp only [selected]
    split
    · exact .cons_cons a (ih _)
    · exact .cons a (ih _)

theorem selected_mem (seen : List (Word W)) (xs : List Hit) {a : Hit}
    (h : a ∈ selected V seen xs) : a ∈ xs :=
  (selected_sublist V seen xs).subset h

theorem selected_length_le (seen : List (Word W)) (xs : List Hit) :
    (selected V seen xs).length ≤ xs.length :=
  (selected_sublist V seen xs).length_le

theorem mem_selectedKeys_iff (seen : List (Word W)) (xs : List Hit) (y : Word W) :
    y ∈ (selected V seen xs).map (fun a => V a.key) ↔
      y ≠ 0 ∧ y ∉ seen ∧ y ∈ xs.map (fun a => V a.key) := by
  induction xs generalizing seen with
  | nil => simp [selected]
  | cons a xs ih =>
    by_cases fresh : V a.key ≠ 0 ∧ V a.key ∉ seen
    · simp only [selected, ite_eq_left fresh, List.map_cons, List.mem_cons, ih]
      by_cases same : y = V a.key
      · subst y
        simp [fresh.1, fresh.2]
      · simp [same]
    · simp only [selected, ite_eq_right fresh, List.map_cons, List.mem_cons, ih]
      by_cases same : y = V a.key
      · subst y
        simp [fresh]
      · simp [same]

theorem exists_selected_with_key_iff (seen : List (Word W)) (xs : List Hit) (y : Word W)
    (nonzero : y ≠ 0) (unseen : y ∉ seen) :
    (∃ a ∈ selected V seen xs, V a.key = y) ↔ ∃ a ∈ xs, V a.key = y := by
  constructor
  · rintro ⟨a, ha, key⟩
    exact ⟨a, selected_mem V seen xs ha, key⟩
  · intro found
    exact List.mem_map.mp ((mem_selectedKeys_iff V seen xs y).2
      ⟨nonzero, unseen, List.mem_map.mpr found⟩)

theorem selectedKeys_nodup (seen : List (Word W)) (xs : List Hit) :
    ((selected V seen xs).map (fun a => V a.key)).Nodup := by
  induction xs generalizing seen with
  | nil => simp [selected]
  | cons a xs ih =>
    by_cases fresh : V a.key ≠ 0 ∧ V a.key ∉ seen
    · simp only [selected, ite_eq_left fresh, List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, ih _⟩
      exact ((mem_selectedKeys_iff V (V a.key :: seen) xs (V a.key)).mp h).2.1 List.mem_cons_self
    · simpa only [selected, ite_eq_right fresh] using ih (V a.key :: seen)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end OAI
