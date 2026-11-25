import OAI.Hierarchy.FactorSchedule

namespace OAI
/-! # Recovering the tick assigned to each labelled factor occurrence -/

namespace Hierarchy.FactorAllocation

private theorem sum_indicator {α : Type*} [DecidableEq α] (x : α) (xs : List α) :
    (xs.map (fun a => if x = a then (1:ℕ) else 0)).sum = xs.count x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases e : x = a
    · subst a
      simp [ih, Nat.add_comm]
    · simp [e, List.count_cons_of_ne (Ne.symm e), ih]

/-- Conservation applies even to indicator weights on distinct input occurrences. -/
theorem count_total {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ) (i : Fin N) :
    (∑ t : Fin T, (factors w cost (List.finRange N) t).count i) = 1 := by
  have h := sum_factors_all ht w cost (List.finRange N) (fun a => if i=a then (1:ℕ) else 0)
  simp_rw [sum_indicator] at h
  simpa using h

theorem unique_tick {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ) (i : Fin N) :
    ∃! t : Fin T, i ∈ factors w cost (List.finRange N) t := by
  let occ (t : Fin T) := (factors w cost (List.finRange N) t).count i
  have total : ∑ t, occ t = 1 := count_total ht w cost i
  obtain ⟨t, positive⟩ : ∃ t, 0 < occ t := by
    by_contra! h
    have allzero (t) : occ t=0 := Nat.eq_zero_of_le_zero (h t)
    simp [allzero] at total
  have split := Finset.sum_erase_add (s:=Finset.univ) occ (Finset.mem_univ t)
  have rest : ∑ u ∈ (Finset.univ.erase t), occ u = 0 := by omega
  refine ⟨t, List.count_pos_iff.mp positive, ?_⟩
  intro u hu
  by_contra hne
  have lower := Finset.single_le_sum (s:=Finset.univ.erase t) (f:=occ)
    (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ u⟩)
  have more : 0 < occ u := List.count_pos_iff.mpr hu
  omega

theorem factors_nodup {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ) (t : Fin T) :
    (factors w cost (List.finRange N) t).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro i
  rw [← count_total ht w cost i]
  exact Finset.single_le_sum (f:=fun u => (factors w cost (List.finRange N) u).count i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)

/-- Compute the owner's tick by finite search through the assigned lists. -/
def owner {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ) (i : Fin N) : Fin T :=
  (Finset.univ.filter (fun t : Fin T => i ∈ factors w cost (List.finRange N) t)).min' (by
    obtain ⟨t,h,_⟩ := unique_tick ht w cost i
    exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

theorem mem_factors_iff_owner {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ)
    (i : Fin N) (t : Fin T) :
    i ∈ factors w cost (List.finRange N) t ↔ t = owner ht w cost i := by
  have found : i ∈ factors w cost (List.finRange N) (owner ht w cost i) := by
    unfold owner
    exact (Finset.mem_filter.mp (Finset.min'_mem
      (Finset.univ.filter (fun t : Fin T => i ∈ factors w cost (List.finRange N) t)) _)).2
  exact ⟨fun h => (unique_tick ht w cost i).unique h found, fun e => e ▸ found⟩

/-- Each original rail has one owning factor. The number sent to a tick
in a direction equals the sum of that direction's charges on the ordered
list the tick receives. -/
theorem fiber_conservation {N T d k : ℕ} {E : Type*} [Fintype E] (ht : 0<T) (w : ℕ)
    (cost : Fin N → Fin d → ℕ) (origin : E → Fin N) (direction : E → Fin k)
    (coord : Fin k → Fin d)
    (account : ∀ i j, (Finset.univ.filter (fun e => direction e=j ∧ origin e=i)).card = cost i (coord j))
    (j : Fin k) (t : Fin T) :
    (Finset.univ.filter (fun e => direction e=j ∧ owner ht w cost (origin e)=t)).card =
      ((factors w cost (List.finRange N) t).map (fun i => cost i (coord j))).sum := by
  classical
  let xs := factors w cost (List.finRange N) t
  let assigned := Finset.univ.filter (fun e => direction e=j ∧ owner ht w cost (origin e)=t)
  have maps : (assigned : Set E).MapsTo origin xs.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr ((mem_factors_iff_owner ht w cost _ _).mpr
      (Finset.mem_filter.mp he).2.2.symm)
  change assigned.card = (xs.map (fun i => cost i (coord j))).sum
  rw [Finset.card_eq_sum_card_fiberwise maps, ← List.sum_toFinset _ (factors_nodup ht w cost t)]
  apply Finset.sum_congr rfl
  intro i hi
  have own := (mem_factors_iff_owner ht w cost i t).mp (List.mem_toFinset.mp hi)
  rw [← account i j]
  congr 1
  ext e
  simp only [assigned, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hd,_⟩,he⟩
    exact ⟨hd,he⟩
  · rintro ⟨hd,he⟩
    exact ⟨⟨hd,he ▸ own.symm⟩,he⟩

end Hierarchy.FactorAllocation

end OAI
