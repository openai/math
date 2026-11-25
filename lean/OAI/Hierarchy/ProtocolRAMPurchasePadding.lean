import OAI.Hierarchy.ProtocolRAMPurchaseDFS
import Mathlib.Data.Fin.Embedding

namespace OAI
/-! # Dummy rows in the fixed-width sampler purchase scan -/

namespace Hierarchy.ProtocolRAM.PurchaseDFS

open AdaptiveProbe

variable {n D h : ℕ}

/-- Invalid words are represented by a path entirely on the last, permanently unavailable row. -/
def fillOption (h : ℕ) (p : Option (List (Fin n))) : List (Fin (n+1)) :=
  p.elim (List.replicate (h+1) (Fin.last n)) (List.map Fin.castSucc)

def normalized (choice : Fin n → Fin D → Option (Fin n)) (z : Fin n × (Fin h → Fin D)) :=
  (walk choice z.1 z.2).filter (fun p => decide p.Nodup)

def filled (choice : Fin n → Fin D → Option (Fin n)) (z : Fin n × (Fin h → Fin D)) :=
  fillOption h (normalized choice z)

@[simp] theorem filled_length (choice : Fin n → Fin D → Option (Fin n))
    (z : Fin n × (Fin h → Fin D)) : (filled choice z).length = h+1 := by
  cases eq : normalized choice z with
  | none => simp [filled,eq,fillOption]
  | some p =>
    have hm : p ∈ candidates choice h := by
      rw [candidates_eq_filterMap]
      exact List.mem_filterMap.mpr ⟨z,mem_layout z.1 z.2,eq⟩
    simpa [filled,eq,fillOption] using ((mem_candidates choice).mp hm).1

private theorem sequence_cases {α : Type*} (xs : List (Option α)) :
    (none ∈ xs ∧ xs.mapM id = none) ∨ ∃ ys : List α, xs = ys.map some ∧ xs.mapM id = some ys := by
  induction xs with
  | nil => exact Or.inr ⟨[],rfl,rfl⟩
  | cons x xs ih =>
    cases x with
    | none => exact Or.inl ⟨by simp, by simp⟩
    | some a =>
      rcases ih with ⟨hn,hs⟩ | ⟨ys,rfl,hs⟩
      · exact Or.inl ⟨List.mem_cons_of_mem _ hn,by simp [hs]⟩
      · exact Or.inr ⟨a::ys,rfl,by simp [hs]⟩

private theorem fill_sequence (vs : List (Option (Fin n))) (len : vs.length = h+1) :
    fillOption h ((vs.mapM id).filter (fun p => decide p.Nodup)) =
    vs.map (fun v => if none ∉ vs ∧ vs.Nodup then v.elim (Fin.last n) Fin.castSucc else Fin.last n) := by
  rcases sequence_cases vs with ⟨hn,hs⟩ | ⟨ys,rfl,hs⟩
  · simp [hs,hn,fillOption,len]
  · have yslen : ys.length = h+1 := by simpa using len
    have live : none ∉ ys.map some := by simp
    have simpPaths : (ys.map some).Nodup ↔ ys.Nodup := List.nodup_map_iff (Option.some_injective _)
    by_cases distinct : ys.Nodup <;>
      simp [hs, live, simpPaths, distinct, fillOption, Option.filter, Function.comp_def, yslen]

/-- The fixed-H materialization, column by column, from the optional physical row states. -/
theorem filled_eq_state_rows (choice : Fin n → Fin D → Option (Fin n))
    (z : Fin n × (Fin h → Fin D)) : filled choice z = List.ofFn (fun j : Fin (h+1) =>
      let vs := optionStates choice (some z.1) (List.ofFn z.2)
      let v := vs[j.val]'(by simpa [vs] using j.isLt)
      if none ∉ vs ∧ vs.Nodup then v.elim (Fin.last n) Fin.castSucc else Fin.last n) := by
  let vs := optionStates choice (some z.1) (List.ofFn z.2)
  have len : vs.length = h+1 := by simp [vs]
  rw [filled,normalized,←optionStates_walk,fill_sequence vs len]
  apply List.ext_getElem
  · simp [len]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_ofFn, vs]

private theorem row_map (p : List (Fin n)) :
    (p.map Fin.castSucc).toFinset = p.toFinset.map Fin.castSuccEmb := by
  ext x
  simp [Finset.mem_map, List.mem_map, Fin.castSuccEmb_apply]

private theorem dummy_rejected (h : ℕ) (left : Finset (Fin n)) :
    ¬ (fillOption h (none : Option (List (Fin n)))).toFinset ⊆ left.map Fin.castSuccEmb := by
  intro accept
  have member : Fin.last n ∈ (fillOption h (none : Option (List (Fin n)))).toFinset := by
    simp [fillOption]
  obtain ⟨v,_,eq⟩ := Finset.mem_map.mp (accept member)
  exact (Fin.ne_of_lt (Fin.castSucc_lt_last v)) eq

/-- Erasing rejected dummy rows commutes with the entire ordered greedy scan. -/
theorem scan_options (h : ℕ) (xs : List (Option (List (Fin n)))) (left : Finset (Fin n)) :
    scanPaths (xs.map (fillOption h)) (left.map Fin.castSuccEmb) =
      (((scanPaths xs.reduceOption left).1.map (List.map Fin.castSucc)),
        (scanPaths xs.reduceOption left).2.map Fin.castSuccEmb) := by
  induction xs generalizing left with
  | nil => rfl
  | cons o xs ih =>
    cases o with
    | none =>
      simp only [List.map_cons, List.reduceOption_cons_of_none, scanPaths, ite_eq_right (dummy_rejected h left)]
      exact ih left
    | some p =>
      simp only [List.map_cons, List.reduceOption_cons_of_some]
      change scanPaths (p.map Fin.castSucc :: _) _ = _
      by_cases usable : p.toFinset ⊆ left
      · simp only [scanPaths, row_map, Finset.map_subset_map, ite_eq_left usable, ←Finset.map_sdiff,
          ih, List.map_cons]
      · simp only [scanPaths, row_map, Finset.map_subset_map, ite_eq_right usable, ih]

/-- Canonical padded IDs yield the same purchases and remaining rows as the normalized scan. -/
theorem scan_filled (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) (left : Finset (Fin n)) :
    scanPaths ((layout n D h).map (filled choice)) (left.map Fin.castSuccEmb) =
      (((scanPaths (candidates choice h) left).1.map (List.map Fin.castSucc)),
        (scanPaths (candidates choice h) left).2.map Fin.castSuccEmb) := by
  let rows := (layout n D h).map (normalized choice)
  have expand : rows.map (fillOption h) = (layout n D h).map (filled choice) := by
    dsimp only [rows]
    rw [List.map_map]; rfl
  have valid : rows.reduceOption = candidates choice h := by
    rw [candidates_eq_filterMap]
    change ((layout n D h).map (normalized choice)).filterMap id = _
    rw [List.filterMap_map]; rfl
  rw [← expand, ← valid]
  exact scan_options h rows left

/-- At a particular padded ID the physical purchase flag is true exactly when a normalized
candidate exists and its original rows are all still available after the preceding IDs. -/
theorem filled_accepted_after (choice : Fin n → Fin D → Option (Fin n))
    (earlier : List (Fin n × (Fin h → Fin D))) (z : Fin n × (Fin h → Fin D)) (left : Finset (Fin n)) :
    (filled choice z).toFinset ⊆ (scanPaths (earlier.map (filled choice)) (left.map Fin.castSuccEmb)).2 ↔
      ∃ p, normalized choice z = some p ∧
        p.toFinset ⊆ (scanPaths (earlier.filterMap (normalized choice)) left).2 := by
  have prev := congrArg Prod.snd (scan_options h (earlier.map (normalized choice)) left)
  simp only [List.map_map, Function.comp_def, List.reduceOption, List.filterMap_map, id_eq] at prev
  change (fillOption h (normalized choice z)).toFinset ⊆ _ ↔ _
  rw [show (scanPaths (earlier.map (filled choice)) (left.map Fin.castSuccEmb)).2 = _ from prev]
  cases et : normalized choice z with
  | none => simp [dummy_rejected]
  | some p => simp [fillOption,row_map,Finset.map_subset_map]


end Hierarchy.ProtocolRAM.PurchaseDFS

end OAI
