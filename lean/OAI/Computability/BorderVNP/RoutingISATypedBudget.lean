import OAI.Computability.BorderVNP.RoutingISATypedTeam

/-! # Total burst charge of the physically prepared cell rows

Each owned call has one of the locally prepared pointers. Different calls occupy
different three-word rows, hence use different tasks. Summing the word lengths of
these actual calls is bounded by the sum of all lengths emitted by the local batch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM CellDispatch CompactMachine

/-- The true directory charge reads every locally assigned packed argument at most once. -/
theorem PlacedRows.total_burst_le {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (placed : PlacedRows pub m tasks count n cells)
    (layout : Allocated w table count tasks) (room : ∀ i < count, (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) :
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ((f.ownedRows mt 0 f.count).map (fun i => (mt (f.address i+2)).val)).sum ≤
      ∑ j ∈ Finset.range count, ((tasks j).cell.burst w).length := by
  classical
  intro f mt
  let rows := f.ownedRows mt 0 f.count
  have listed (i : ℕ) (hi : i ∈ rows) : i < f.count ∧ (m (f.address i)).val = f.team := by
    obtain ⟨h,own⟩ := List.mem_filter.mp hi
    have hlt : i < f.count := by simpa using h
    have owner : mt (f.address i) = m (f.address i) := control.survives.2 i hlt
    exact ⟨hlt,by simpa only [decide_eq_true_eq,owner] using own⟩
  have assigned (i : ℕ) (hi : i ∈ rows) := placed.task i (listed i hi).1 (listed i hi).2
  let pick (i : ℕ) := if hi : i ∈ rows then (assigned i hi).choose else 0
  have picked (i : ℕ) (hi : i ∈ rows) : pick i < count ∧ (tasks (pick i)).callRow = f.address i := by
    simp only [pick,dite_eq_left hi]
    exact ⟨(assigned i hi).choose_spec.1,(assigned i hi).choose_spec.2.1⟩
  have q (i : ℕ) (hi : i ∈ rows) :
      (mt (f.address i+2)).val = ((tasks (pick i)).cell.burst w).length := by
    obtain ⟨h,row⟩ := picked i hi
    rw [← row]
    exact (layout.output_words m _ h (room _ h)).2.1
  have nodup : rows.Nodup := List.Nodup.filter _ (List.nodup_range' ..)
  have inj : Set.InjOn pick rows.toFinset := by
    intro i hi k hk eq
    have a := (picked i (List.mem_toFinset.mp hi)).2
    have b := (picked k (List.mem_toFinset.mp hk)).2
    rw [eq,b] at a
    simp [Frame.address] at a
    omega
  calc
    _ = ∑ i ∈ rows.toFinset, (mt (f.address i+2)).val := (List.sum_toFinset _ nodup).symm
    _ = ∑ i ∈ rows.toFinset, ((tasks (pick i)).cell.burst w).length :=
      Finset.sum_congr rfl (fun i hi => q i (List.mem_toFinset.mp hi))
    _ = ∑ j ∈ rows.toFinset.image pick, ((tasks j).cell.burst w).length := (Finset.sum_image (f := fun j => ((tasks j).cell.burst w).length) inj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (picked i (List.mem_toFinset.mp hi)).1)

/-- Every owned row in final memory retains the cap on its own physically constructed burst. -/
theorem PlacedRows.final_cap {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (placed : PlacedRows pub m tasks count n cells)
    (layout : Allocated w table count tasks) (room : ∀ i < count, (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) :
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∀ i < f.count, (mt (f.address i)).val=f.team → (mt (f.address i+2)).val ≤ TeamScales.width n (1/2) := by
  intro f mt i hi own
  have owner := control.survives.2 i hi
  obtain ⟨j,hj,row,_⟩ := placed.task i hi (by simpa only [← owner] using own)
  rw [← row,(layout.output_words m j hj (room j hj)).2.1]
  exact placed.cap j hj

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
