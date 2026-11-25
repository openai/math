import OAI.Computability.BorderVNP.PrivatePlacementPass

/-! # Running counts and output slots in the private placement pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.PrivatePlacement

/-- Concrete frame words needed to initialize the placement registers. -/
structure Layout.Fields (l : Layout) (before : ℕ → ℕ) : Prop where
  /-- Placement pointer, number of original sites, and description width. -/
  raw : before (l.frame+64) = l.raw ∧ before (l.frame+66) = l.entries ∧ before (l.frame+69) = l.desc
  /-- Incidence pointer, cell count, and cable count. -/
  geometry : before (l.frame+87) = l.incidence ∧ before (l.frame+11) = l.cells ∧ before (l.frame+7) = l.cables
  /-- The task-control subdirectory stores the reserved tail capacity at offset eight. -/
  gap : before (before (l.frame+92)+8) = l.gap

/-- Word fit and separation of the three addressed arrays. -/
structure Layout.Fits (l : Layout) (w : ℕ) (before : ℕ → ℕ) : Prop where
  /-- Frame fields fit their physical addresses. -/
  frame : l.frame+92 < 2^w
  /-- The tail-capacity word in the secondary control directory is addressable. -/
  control : before (l.frame+92)+8 < 2^w
  /-- The initialized scratch pointer fits even when its array is empty. -/
  base : l.scratch < 2^w
  /-- Both count arrays fit, including the last scratch cell. -/
  counts : l.scratch+l.cells ≤ 2^w
  /-- Every two-word raw placement record is addressable. -/
  raw : l.raw+2*l.entries ≤ 2^w
  /-- Placements are outside both consecutive count arrays. -/
  apart : l.scratch+l.cells ≤ l.raw ∨ l.raw+2*l.entries ≤ l.supplied
  /-- Each genuine record names a final cell. -/
  owners : ∀ i < l.entries, l.owner before i < l.cells
  /-- The two values stored for this record are representable machine words. -/
  values : ∀ i < l.entries, let c := l.owner before i
    let n := prefixCounts (l.owner before) l.desc i c
    before (l.supplied+c)+l.gap+n < 2^w ∧ n+l.desc < 2^w

/-- Exact partial output, running count for every cell, and every untouched word. -/
structure Layout.Image (l : Layout) (before : ℕ → ℕ) (i : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Every counter is the total width of the already visited descriptions for that cell. -/
  counters : ∀ c < l.cells, mem (l.scratch+c) = prefixCounts (l.owner before) l.desc i c
  /-- Completed slots follow the supplied inputs and the reserved report-tail capacity for each cell. -/
  slots : ∀ j < i, let c := l.owner before j
    mem (l.raw+2*j+1) = before (l.supplied+c)+l.gap+prefixCounts (l.owner before) l.desc j c
  /-- The entire complement of the counters and populated slot words is preserved. -/
  outside : ∀ x, (∀ j < i, x ≠ l.raw+2*j+1) → (x < l.scratch ∨ l.scratch+l.cells ≤ x) → mem x = before x

private theorem apart (l : Layout) {w : ℕ} {before : ℕ → ℕ} (fit : l.Fits w before)
    {x : ℕ} (lo : l.raw ≤ x) (hi : x < l.raw+2*l.entries) :
    x < l.supplied ∨ l.scratch+l.cells ≤ x := by rcases fit.apart with h|h <;> omega

/-- The first word of each record retains its original destination cell. -/
theorem Layout.Image.owner_eq {l : Layout} {before mem : ℕ → ℕ} {i j w : ℕ}
    (image : l.Image before i mem) (fit : l.Fits w before) (hj : j < l.entries) :
    mem (l.raw+2*j) = l.owner before j := by
  apply image.outside _ (fun k _ => by omega)
  have := apart l fit (x := l.raw+2*j) (by omega) (by omega)
  dsimp only [Layout.scratch] at *
  omega

/-- The supplied-count array survives all writes by the placement pass. -/
theorem Layout.Image.supplied_eq {l : Layout} {before mem : ℕ → ℕ} {i w c : ℕ}
    (image : l.Image before i mem) (fit : l.Fits w before) (hi : i ≤ l.entries) (hc : c < l.cells) :
    mem (l.supplied+c) = before (l.supplied+c) := by
  apply image.outside
  · intro j hj
    have := apart l fit (x := l.raw+2*j+1) (by omega) (by omega)
    dsimp only [Layout.scratch] at *
    omega
  · left; dsimp only [Layout.scratch]; omega

private theorem prefix_next (owner : ℕ → ℕ) (desc i c : ℕ) :
    prefixCounts owner desc (i+1) c = prefixCounts owner desc i c + if owner i=c then desc else 0 :=
  Finset.sum_range_succ ..

/-- The two stores extend the exact placement image by one original site. -/
theorem Layout.Image.step {l : Layout} {before mem : ℕ → ℕ} {i w : ℕ}
    (image : l.Image before i mem) (fit : l.Fits w before) (hi : i < l.entries) :
    let c := l.owner before i
    let n := prefixCounts (l.owner before) l.desc i c
    l.Image before (i+1) (Function.update (Function.update mem (l.raw+2*i+1)
      (before (l.supplied+c)+l.gap+n)) (l.scratch+c) (n+l.desc)) := by
  intro c n
  have hc : c < l.cells := fit.owners i hi
  have sep {j b : ℕ} (hj : j < l.entries) (hb : b < l.cells) : l.raw+2*j+1 ≠ l.scratch+b := by
    have := apart l fit (x := l.raw+2*j+1) (by omega) (by omega)
    dsimp only [Layout.scratch] at *
    omega
  constructor
  · intro b hb
    rw [prefix_next]
    by_cases eq : c=b
    · subst b
      rw [Function.update_self,ite_eq_left (show l.owner before i = c from rfl)]
    · rw [ite_eq_right eq,Nat.add_zero,Function.update_of_ne (by omega : l.scratch+b ≠ l.scratch+c),
        Function.update_of_ne (sep hi hb).symm,image.counters b hb]
      exact (Nat.add_zero _).symm
  · intro j hj
    rw [Function.update_of_ne (sep (by omega : j < l.entries) hc)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
    · rw [Function.update_of_ne (by omega : l.raw+2*j+1 ≠ l.raw+2*i+1)]
      exact image.slots j hj
    · exact Function.update_self ..
  · intro x notSlot notCounter
    rw [Function.update_of_ne (by omega : x ≠ l.scratch+c),Function.update_of_ne (notSlot i i.lt_succ_self)]
    exact image.outside x (fun j hj => notSlot j (hj.trans i.lt_succ_self)) notCounter

end RoutingISA.PrivatePlacement

end BorderVNP
end Computability
end OAI
