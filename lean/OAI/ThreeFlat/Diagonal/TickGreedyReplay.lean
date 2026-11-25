import OAI.ThreeFlat.Diagonal.Scheduling

namespace OAI
/-! # Streaming the greedy group and processor-slot assignments -/

namespace ThreeFlat.Diagonal.TickGreedyReplay

open LinearAlgebra.SpectralBooks.VNP
variable {α : Type*}

/-- The current zero-based bucket number and its remaining tick capacity. -/
abbrev Cursor := ℕ × ℕ

/-- Crossing a capacity boundary advances the bucket before charging the item. -/
def place (cap : ℕ) (s : Cursor) (weight : ℕ) : Cursor :=
  if weight ≤ s.2 then (s.1,s.2-weight) else (s.1+1,cap-weight)

/-- Emit each input in order with its owner, updating just two counters. -/
def assign (cost : α → ℕ) (cap : ℕ) (s : Cursor) : List α → List (ℕ × α)
  | [] => []
  | x::xs =>
    let s' := place cap s (cost x)
    (s'.1,x) :: assign cost cap s' xs

/-- Enumerate a padded block list, emitting no item for an empty block. -/
def label (i : ℕ) : List (List α) → List (ℕ × α)
  | [] => []
  | b::bs => b.map (fun x => (i,x)) ++ label (i+1) bs

private theorem within (cost : α → ℕ) (cap i left : ℕ) (b tail : List α)
    (fits : Team.ticks cost b ≤ left) :
    assign cost cap (i,left) (b++tail) = b.map (fun x => (i,x)) ++
      assign cost cap (i,left-Team.ticks cost b) tail := by
  induction b generalizing left with
  | nil => simp
  | cons x xs ih =>
    simp only [Team.ticks_cons] at fits
    have hx : cost x ≤ left := by omega
    simp only [List.cons_append,assign,place,ite_eq_left hx,List.map_cons,List.cons.injEq,true_and,
      Team.ticks_cons]
    simpa only [Nat.sub_sub] using ih (left-cost x) (by omega)

private theorem assign_valid (cost : α → ℕ) (cap idx : ℕ) (xs : List α) (bs : List (List α))
    (ok : Team.ValidHandoff cost cap xs bs []) (small : ∀ x ∈ xs, cost x ≤ cap) :
    assign cost cap (idx,cap) xs = label idx bs := by
  induction bs generalizing idx xs with
  | nil => change [] = xs at ok; subst xs; rfl
  | cons b bs ih =>
    obtain ⟨tail,rfl,hm,rest⟩ := ok
    have st (x : α) (hx : x ∈ tail) : cost x ≤ cap := small x (List.mem_append_right _ hx)
    have switch : assign cost cap (idx,cap-Team.ticks cost b) tail =
        assign cost cap (idx+1,cap) tail := by
      cases tail with
      | nil => rfl
      | cons x xs =>
        have notFit : ¬cost x ≤ cap-Team.ticks cost b := by
          have hx := hm.2 x xs rfl
          have hb := hm.1
          omega
        simp [assign,place,notFit,st x List.mem_cons_self]
    rw [within cost cap idx cap b tail hm.1, switch, ih (idx+1) tail rest st, label]

/-- Convert a packed-block conclusion, as returned by `schedule_at_collapse_scales`,
to the remainder condition used by the one-pass scan. -/
theorem remainder_nil_of_flatten {cost : α → ℕ} {cap count : ℕ} {xs : List α}
    (covered : (Team.handoff cost cap count xs).1.flatten = xs) :
    (Team.handoff cost cap count xs).2 = [] := by
  have flat := Team.handoff_flatten cost cap count xs
  rw [covered] at flat
  have len := congrArg List.length flat
  simp only [List.length_append] at len
  apply List.eq_nil_of_length_eq_zero
  omega

/-- A single left-to-right pass gives exactly the padded handoff's owner for
each cell. The comparison uses the same non-strict capacity test. -/
theorem assign_handoff (cost : α → ℕ) (cap count : ℕ) (xs : List α)
    (small : ∀ x ∈ xs, cost x ≤ cap) (complete : (Team.handoff cost cap count xs).2 = []) :
    assign cost cap (0,cap) xs = label 0 (Team.handoff cost cap count xs).1 := by
  apply assign_valid cost cap 0 xs _ _ small
  simpa only [complete] using Team.handoff_valid cost cap count xs

theorem assign_groups {J W B : ℕ} (hJ : 0 < J) (hW : 0 < W) (hB : 0 < B)
    (work pairs : α → ℕ) (xs : List α)
    (pos : ∀ x ∈ xs, 0 < work x) (wt : Team.ticks work xs ≤ W) (pt : Team.ticks pairs xs ≤ B)
    (small : ∀ x ∈ xs, cellScore J W B work pairs x ≤ 2*(W*B)) :
    assign (cellScore J W B work pairs) (4*(W*B)) (0,4*(W*B)) xs =
      label 0 (schedule J W B work pairs xs) := by
  let score := cellScore J W B work pairs
  let cap := 4*(W*B)
  have packed := (schedule_spec hJ hW hB work pairs xs pos wt pt small).2.1
  change (Team.handoff score cap J xs).1.flatten = xs at packed
  apply assign_handoff score cap J xs (fun x hx => by
    have := small x hx
    change cellScore J W B work pairs x ≤ 4*(W*B)
    omega)
  exact remainder_nil_of_flatten packed

/-- For processor slots the same counters use the work cost and capacity `m/4`. -/
theorem assign_slots (work : α → ℕ) (m teams : ℕ) (group : List α)
    (small : ∀ x ∈ group, work x ≤ m/4) (complete : (Team.handoff work (m/4) teams group).2 = []) :
    assign work (m/4) (0,m/4) group = label 0 (Team.handoff work (m/4) teams group).1 :=
  assign_handoff work (m/4) teams group small complete

end ThreeFlat.Diagonal.TickGreedyReplay

end OAI
