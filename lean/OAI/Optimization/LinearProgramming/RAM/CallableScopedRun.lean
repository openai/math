import OAI.Optimization.LinearProgramming.RAM.CallableScopedSteps

/-! Relocatable calls in a finite window. Neither startup literals in the caller nor native
return program counters contribute to these memory caps. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Fragment

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {f : Fragment} {P : K→Prop} {m t : Memory K} {bound b cap : ℕ}

/-- Trim an ideal address bank to the finite working window at every installation site. -/
theorem Run.trim (run : f.Run P m bound t) (localCode : f.Scoped b) (start : ∀ j,m.index j≤b)
    (room : b+bound≤cap) : f.Run P (trimMemory cap m) bound (trimMemory cap t) := by
  intro prog pc code
  let sub := clampProgram b prog
  obtain ⟨k,hk,work⟩ := run sub pc (clampProgram_code localCode code)
  obtain ⟨tr,ht,he,hs⟩ := work.to_trace
  have body := trace_trim_access (fun _ hi => clampProgram_budget prog b hi) start ht
    ((Nat.add_le_add_left hk b).trans room)
  have exec := Execution.of_trace (safe := fun st => ∀ j,P (st.data j)) body (fun i => hs i)
  change Execution sub _ _ k (trimIndex cap (tr (Fin.last k))) at exec
  rw [he] at exec
  exact ⟨k,hk,replay_clamped exec rfl⟩

/-- Splice the exact local trace into a larger scalar and index heap. Every address beyond
`cap` preserves the caller's data while the same fixed fragment executes at arbitrary PCs. -/
theorem Run.run_window (run : f.Run P m bound t) (localCode : f.Scoped b) (start : ∀ j,m.index j≤b)
    (room : b+bound≤cap) (tail : Memory K) (tailSafe : ∀ j,cap<j → P (tail.data j)) :
    f.Run P (windowMemory cap tail m) bound (windowMemory cap tail t) := by
  intro prog pc code
  let sub := clampProgram b prog
  obtain ⟨k,hk,work⟩ := run sub pc (clampProgram_code localCode code)
  obtain ⟨tr,ht,he,hs⟩ := work.to_trace
  have body := trace_window_access tail (fun _ hi => clampProgram_budget prog b hi) start ht
    ((Nat.add_le_add_left hk b).trans room)
  have safe (i : Fin (k+1)) (j : ℕ) : P ((windowState cap tail (tr i)).data j) := by
    change P (if j≤cap then (tr i).data j else tail.data j)
    split_ifs with inside
    · exact hs i j
    · exact tailSafe j (by omega)
  have exec := Execution.of_trace (safe := fun st => ∀ j,P (st.data j)) body safe
  change Execution sub _ _ k (windowState cap tail (tr (Fin.last k))) at exec
  rw [he] at exec
  exact ⟨k,hk,replay_clamped exec rfl⟩

/-- The logical worker's final address maximum is also independent of its containing program. -/
theorem Run.final_index_bound (run : f.Run P m bound t) (localCode : f.Scoped b) (start : ∀ j,m.index j≤b) :
    ∀ j,t.index j≤b+bound := by
  obtain ⟨k,hk,work⟩ := run (f.emit 0) 0 (CodeAt.whole _)
  obtain ⟨tr,hw,he,_⟩ := work.to_trace
  have h := trace_access_indexBound (localCode 0) start hw (Fin.last k)
  rw [he] at h
  exact fun j => (h j).trans (Nat.add_le_add_left hk b)

/-- Direct finite-start rule for an assembled worker. The normal-entry boot code may
compute this cap using only its input's maximum address, its worker, and its time bound. -/
theorem Run.fixed_trim [FixedAccess f] (run : f.Run P m bound t) (start : ∀ j,m.index j≤b)
    (room : max f.localBudget b + bound≤cap) : f.Run P (trimMemory cap m) bound (trimMemory cap t) :=
  run.trim ((scoped_localBudget f).mono (le_max_left _ _)) (fun j => (start j).trans (le_max_right _ _)) room

theorem Run.fixed_window [FixedAccess f] (run : f.Run P m bound t) (start : ∀ j,m.index j≤b)
    (room : max f.localBudget b + bound≤cap) (tail : Memory K) (tailSafe : ∀ j,cap<j → P (tail.data j)) :
    f.Run P (windowMemory cap tail m) bound (windowMemory cap tail t) :=
  run.run_window ((scoped_localBudget f).mono (le_max_left _ _)) (fun j => (start j).trans (le_max_right _ _))
    room tail tailSafe

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
