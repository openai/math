import OAI.Computability.BorderVNP.RoutingISATableBounds

/-! # Partial memory images for the nested offset-table scan

Two row-major cursors count the completed triple offsets and pair totals.
Stores never change addresses outside these two arrays. The width table is
therefore readable throughout the nested pass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- The computed triple and pair prefixes, together with frame preservation. -/
structure OffsetMemory (l : TableLayout) (row : ℕ → TableRow) (old mem : ℕ → ℕ)
    (off used : ℕ) : Prop where
  /-- All earlier partner offsets have been written. -/
  front : ∀ u < l.teams, ∀ v < l.teams, ∀ j < l.teams, (u*l.teams+v)*l.teams+j < off →
    mem (tripleIndex l.offsets l.teams u v j) = l.legPrefix row u v j
  /-- All earlier oriented leg totals have been written. -/
  total : ∀ u < l.teams, ∀ v < l.teams, u*l.teams+v < used →
    mem (pairIndex l.used l.teams u v) = l.legPrefix row u v l.teams
  /-- Every address outside the two output arrays retains its original word. -/
  other : ∀ i, ¬ l.contains .offsets i → ¬ l.contains .used i → mem i = old i

variable {l : TableLayout} {row : ℕ → TableRow} {old mem : ℕ → ℕ} {off used w : ℕ}

theorem OffsetMemory.empty : OffsetMemory l row old old 0 0 := by
  constructor <;> intros <;> omega

private theorem unpack {R u v i j : ℕ} (hv : v < R) (hj : j < R)
    (h : u*R+v=i*R+j) : u=i ∧ v=j := by
  have hR : 0 < R := by omega
  have hq := congrArg (· / R) h
  have hr := congrArg (· % R) h
  change (u*R+v)/R=(i*R+j)/R at hq
  change (u*R+v)%R=(i*R+j)%R at hr
  simp only [Nat.mul_comm u R, Nat.mul_comm i R, Nat.mul_add_div hR, Nat.div_eq_of_lt hv, Nat.div_eq_of_lt hj, Nat.add_zero] at hq
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hj] at hr
  exact ⟨hq,hr⟩

theorem offset_contains {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams) (hj : j < l.teams) :
    l.contains .offsets (tripleIndex l.offsets l.teams u v j) := by
  simpa only [TableLayout.base, TableLayout.length, tripleIndex, Nat.add_comm l.offsets] using
    l.contains_offset (a := .offsets) (tripleKey_bound hu hv hj)

theorem used_contains {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams) :
    l.contains .used (pairIndex l.used l.teams u v) := by
  simpa only [TableLayout.base, TableLayout.length, pairIndex, Nat.add_comm l.used] using
    l.contains_offset (a := .used) (pairKey_bound hu hv)

/-- The width array is disjoint from both outputs throughout the pass. -/
theorem OffsetMemory.width {i : ℕ} (h : OffsetMemory l row old mem off used)
    (ha : l.Allocated w) (hi : i < l.teams^2) : mem (l.widths+i) = old (l.widths+i) := by
  have hmem : l.contains .widths (l.widths+i) := l.contains_offset hi
  exact h.other _ (ha.separate _ _ _ (by decide) hmem) (ha.separate _ _ _ (by decide) hmem)

/-- Storing the next partner prefix advances exactly the triple cursor. -/
theorem OffsetMemory.store_front {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams)
    (hj : j < l.teams) (ha : l.Allocated w)
    (h : OffsetMemory l row old mem ((u*l.teams+v)*l.teams+j) used) :
    OffsetMemory l row old
      (Function.update mem (tripleIndex l.offsets l.teams u v j) (l.legPrefix row u v j))
      ((u*l.teams+v)*l.teams+j+1) used := by
  have here := offset_contains hu hv hj
  constructor
  · intro a ha' b hb c hc hlt
    by_cases he : (a*l.teams+b)*l.teams+c = (u*l.teams+v)*l.teams+j
    · obtain ⟨hp,rfl⟩ := unpack hc hj he
      obtain ⟨rfl,rfl⟩ := unpack hb hv hp
      exact Function.update_self ..
    · rw [Function.update_of_ne (by unfold tripleIndex; omega)]
      exact h.front a ha' b hb c hc (by omega)
  · intro a ha' b hb hp
    have hn := ha.separate _ _ _ (show TableArray.offsets ≠ .used by decide) here
    have hne : pairIndex l.used l.teams a b ≠ tripleIndex l.offsets l.teams u v j :=
      fun he => hn (he ▸ used_contains ha' hb)
    rw [Function.update_of_ne hne]
    exact h.total a ha' b hb hp
  · intro i h₁ h₂
    have hne : i ≠ tripleIndex l.offsets l.teams u v j := fun he => h₁ (he.symm ▸ here)
    rw [Function.update_of_ne hne]
    exact h.other i h₁ h₂

/-- Storing the terminal oriented leg total advances exactly the pair cursor. -/
theorem OffsetMemory.store_total {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams)
    (ha : l.Allocated w) (h : OffsetMemory l row old mem off (u*l.teams+v)) :
    OffsetMemory l row old
      (Function.update mem (pairIndex l.used l.teams u v) (l.legPrefix row u v l.teams))
      off (u*l.teams+v+1) := by
  have here := used_contains hu hv
  constructor
  · intro a ha' b hb c hc hp
    have hn := ha.separate _ _ _ (show TableArray.used ≠ .offsets by decide) here
    have hne : tripleIndex l.offsets l.teams a b c ≠ pairIndex l.used l.teams u v :=
      fun he => hn (he ▸ offset_contains ha' hb hc)
    rw [Function.update_of_ne hne]
    exact h.front a ha' b hb c hc hp
  · intro a ha' b hb hlt
    by_cases he : a*l.teams+b=u*l.teams+v
    · obtain ⟨rfl,rfl⟩ := unpack hb hv he
      exact Function.update_self ..
    · rw [Function.update_of_ne (by unfold pairIndex; omega)]
      exact h.total a ha' b hb (by omega)
  · intro i h₁ h₂
    have hne : i ≠ pairIndex l.used l.teams u v := fun he => h₂ (he.symm ▸ here)
    rw [Function.update_of_ne hne]
    exact h.other i h₁ h₂

end RoutingISA

end BorderVNP
end Computability
end OAI
