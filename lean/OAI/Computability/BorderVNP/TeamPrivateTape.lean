import OAI.Computability.BorderVNP.TeamSignedStack
import Mathlib.Tactic.DeriveFintype

/-!
# Fixed finite-control simulation of a private multitape computation

A bit track has two stacks and a head bit in the control. A transition fetches
all heads simultaneously, then sweeps the fixed set of tracks to update them.
The sweep takes exactly two stack instructions per track and creates no choices.
Only the original binary branch creates two children.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateTape

open VPVNP.RAMTape

/-- A binary track of a two-sided tape. The nearest neighbor is first in each list.
Unoccupied cells beyond either end are blank (zero). -/
structure Track where
  /-- Cells to the left in nearest-first order. -/
  left : List Bool
  /-- The scanned bit. -/
  head : Bool
  /-- Cells to the right in nearest-first order. -/
  right : List Bool

/-- Write the scanned cell and either stay, move left (`some false`) or move right
(`some true`). -/
def Track.move (t : Track) (write : Bool) : Option Bool → Track
  | none => { t with head := write }
  | some false => ⟨t.left.tail, t.left.head?.getD false, write :: t.right⟩
  | some true => ⟨write :: t.left, t.right.head?.getD false, t.right.tail⟩

/-- Finite table entry, with the head symbols already decoded by the current control. -/
structure Command (Q : Type*) (d : ℕ) where
  /-- Continuing native control state. -/
  next : Q
  /-- Bit written at each scanned position. -/
  write : Fin d → Bool
  /-- Direction of each track, shared by all tracks of a single tape. -/
  direction : Fin d → Option Bool
  deriving Fintype

/-- Signed accepting/rejecting halts, deterministic transitions and binary choices. -/
inductive Choice (Q : Type*) (d : ℕ)
  | halt (accept negative : Bool)
  | one (cmd : Command Q d)
  | two (low high : Command Q d)

/-- A fixed private machine with `d` binary tracks. -/
abbrev Table (Q : Type*) (d : ℕ) := Q → (Fin d → Bool) → Choice Q d

variable {Q : Type*} {d : ℕ}

/-- The complete simultaneous write and motion of one native transition. -/
def Command.apply (cmd : Command Q d) (t : Fin d → Track) : Fin d → Track :=
  fun j => (t j).move (cmd.write j) (cmd.direction j)

/-- Left and right bit-stack indices. -/
abbrev Port (d : ℕ) := Fin d × Bool

/-- The unbounded private tape memory represented by bit stacks. -/
def bank (t : Fin d → Track) : Stacks (Port d)
  | (i, false) => (t i).left
  | (i, true) => (t i).right

/-- The finitely many scanned bits kept in the simulation's control. -/
def heads (t : Fin d → Track) : Fin d → Bool := fun i => (t i).head

/-- Finite simulation phases. A sweep cursor equal to `d` finishes the transition. -/
inductive State (Q : Type*) (d : ℕ) where
  | ready (q : Q) (bits : Fin d → Bool)
  | sweep (cmd : Command Q d) (cursor : Fin (d + 1)) (bits : Fin d → Bool)
  | popSide (cmd : Command Q d) (cursor : Fin d) (side : Bool) (bits : Fin d → Bool)
  | stay (cmd : Command Q d) (cursor : Fin d) (bits : Fin d → Bool)
  deriving Fintype

/-- Elementary bit-stack instructions for one fixed private routine. The state table
and named stacks depend on the machine and alphabet, independently of the time bound. -/
def code (P : Table Q d) : StackCode (Port d) (State Q d)
  | .ready q bs =>
    match P q bs with
    | .halt accept _ => .halt accept
    | .one cmd => .goto (.sweep cmd 0 bs)
    | .two low high => .choose (.sweep low 0 bs) (.sweep high 0 bs)
  | .sweep cmd i bs =>
    if hi : i.val < d then
      let j : Fin d := ⟨i, hi⟩
      match cmd.direction j with
      | none => .goto (.stay cmd j bs)
      | some side => .push (j, !side) (cmd.write j) (.popSide cmd j side bs)
    else .goto (.ready cmd.next bs)
  | .stay cmd j bs => .goto (.sweep cmd j.succ (Function.update bs j (cmd.write j)))
  | .popSide cmd j side bs => .pop (j, side) fun b =>
    .sweep cmd j.succ (Function.update bs j (b.getD false))

/-- The sign of a compiled terminal state. -/
def negative (P : Table Q d) : State Q d → Bool
  | .ready q bs => match P q bs with | .halt _ sign => sign | _ => false
  | _ => false

private def updateLane (cmd : Command Q d) (t : Fin d → Track) (i : Fin d) : Fin d → Track :=
  Function.update t i ((cmd.apply t) i)

private theorem heads_update (cmd : Command Q d) (t : Fin d → Track) (i : Fin d) :
    heads (updateLane cmd t i) = Function.update (heads t) i ((cmd.apply t i).head) := by
  funext j
  by_cases h : j = i <;> simp [h, updateLane, heads]

private theorem bank_stay (cmd : Command Q d) (t : Fin d → Track) (i : Fin d)
    (h : cmd.direction i = none) : bank (updateLane cmd t i) = bank t := by
  funext j
  obtain ⟨j, side⟩ := j
  by_cases hj : j = i <;> cases side <;> simp [bank, updateLane, hj, Command.apply, h, Track.move]

private theorem bank_move (cmd : Command Q d) (t : Fin d → Track) (i : Fin d) (side : Bool)
    (h : cmd.direction i = some side) :
    Function.update (Function.update (bank t) (i, !side) (cmd.write i :: bank t (i, !side)))
      (i, side) ((bank t (i, side)).tail) = bank (updateLane cmd t i) := by
  funext j
  obtain ⟨j, k⟩ := j
  by_cases hj : j = i <;> cases side <;> cases k <;>
    simp [Function.update, bank, updateLane, hj, Command.apply, h, Track.move]

private theorem sweep_lane (P : Table Q d) (cmd : Command Q d) (t : Fin d → Track) (i : Fin d) :
    StackRuns (code P) 2 (.sweep cmd i.castSucc (heads t)) (bank t)
      (.sweep cmd i.succ (heads (updateLane cmd t i))) (bank (updateLane cmd t i)) := by
  cases h : cmd.direction i with
  | none =>
    have step : code P (.sweep cmd i.castSucc (heads t)) = .goto (.stay cmd i (heads t)) := by
      simp [code, i.isLt, h]
    rw [bank_stay cmd t i h, heads_update]
    simp only [Command.apply, h, Track.move]
    exact .cons (.goto step) (.cons (.goto rfl) (.nil ..))
  | some side =>
    have step : code P (.sweep cmd i.castSucc (heads t)) =
        .push (i, !side) (cmd.write i) (.popSide cmd i side (heads t)) := by simp [code, i.isLt, h]
    have hdiff : (i, side) ≠ (i, !side) := by cases side <;> simp
    rw [heads_update, ← bank_move cmd t i side h]
    have hhead : (cmd.apply t i).head = (bank t (i, side)).head?.getD false := by
      cases side <;> simp [Command.apply, h, Track.move, bank]
    rw [hhead]
    refine .cons (.push step) (.cons (.pop rfl) ?_)
    rw [Function.update_of_ne hdiff]
    exact .nil ..

private def partialTape (cmd : Command Q d) (t : Fin d → Track) (p : ℕ) : Fin d → Track :=
  fun j => if j.val < p then cmd.apply t j else t j

private theorem partial_succ (cmd : Command Q d) (t : Fin d → Track) (i : Fin d) :
    partialTape cmd t (i.val + 1) = updateLane cmd (partialTape cmd t i.val) i := by
  funext j
  by_cases he : j = i
  · subst j
    simp [updateLane, partialTape, Command.apply]
  · have hn : j.val ≠ i.val := fun e => he (Fin.ext e)
    have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [partialTape, updateLane, he, hlt]

private theorem sweep_suffix (P : Table Q d) (cmd : Command Q d) (t : Fin d → Track)
    (remaining : ℕ) (i : Fin (d+1)) (h : i.val + remaining = d) :
    StackRuns (code P) (2 * remaining + 1) (.sweep cmd i (heads (partialTape cmd t i.val)))
      (bank (partialTape cmd t i.val)) (.ready cmd.next (heads (cmd.apply t))) (bank (cmd.apply t)) := by
  induction remaining generalizing i with
  | zero =>
    have hi : i.val = d := by omega
    have he : partialTape cmd t i.val = cmd.apply t := by
      funext j; simp [partialTape, hi, j.isLt]
    rw [he]
    exact .cons (.goto (by simp [code, hi])) (.nil ..)
  | succ n ih =>
    let j : Fin d := ⟨i, by omega⟩
    have he : i = j.castSucc := Fin.ext rfl
    have run := (sweep_lane P cmd (partialTape cmd t i.val) j).trans
      (show StackRuns (code P) (2*n+1)
        (.sweep cmd j.succ (heads (updateLane cmd (partialTape cmd t i.val) j)))
        (bank (updateLane cmd (partialTape cmd t i.val) j))
        (.ready cmd.next (heads (cmd.apply t))) (bank (cmd.apply t)) by
          rw [← partial_succ cmd t j]
          exact ih j.succ (by dsimp [j]; omega))
    rw [show 2 * (n+1) + 1 = 2 + (2*n+1) by omega, he]
    exact run

/-- The entire deterministic sweep between native steps. It includes a final jump to
the ready state and has an exact linear-in-tracks cost. -/
theorem sweep_run (P : Table Q d) (cmd : Command Q d) (t : Fin d → Track) :
    StackRuns (code P) (2 * d + 1) (.sweep cmd 0 (heads t)) (bank t)
      (.ready cmd.next (heads (cmd.apply t))) (bank (cmd.apply t)) := by
  have hz : partialTape cmd t 0 = t := by funext j; simp [partialTape]
  simpa only [Fin.val_zero, hz] using sweep_suffix P cmd t d 0 (by simp)

/-- The signed path sum of the native multitape table at a given transition bound. -/
def paths (P : Table Q d) : ℕ → Q → (Fin d → Track) → ℤ
  | 0, _, _ => 0
  | fuel + 1, q, t => match P q (heads t) with
    | .halt accept sign => TeamTape.haltWeight accept sign
    | .one c => paths P fuel c.next (c.apply t)
    | .two low high => paths P fuel low.next (low.apply t) + paths P fuel high.next (high.apply t)

/-- A deterministic sequence of stack moves preserves all remaining signed paths. -/
theorem signedPaths_runs {K R : Type*} [DecidableEq K] {C : StackCode K R} {neg : R → Bool}
    {n : ℕ} {q s q' s'} (h : StackRuns C n q s q' s') (fuel : ℕ) :
    TeamStack.paths C neg (fuel+n) q s = TeamStack.paths C neg fuel q' s' := by
  induction h with
  | nil => rfl
  | cons hs _ ih => cases hs <;> simp_all [TeamStack.paths]

/-- The compiled machine has the same signed multiplicity for every native bound,
even if a binary choice has two equal transition slots. -/
theorem compiled_paths (P : Table Q d) (fuel : ℕ) (q : Q) (t : Fin d → Track) :
    TeamStack.paths (code P) (negative P) (fuel * (2 * d + 2)) (.ready q (heads t)) (bank t) =
      paths P fuel q t := by
  induction fuel generalizing q t with
  | zero => simp [TeamStack.paths, paths]
  | succ f ih =>
    rw [Nat.succ_mul, show f * (2*d+2) + (2*d+2) = (f * (2*d+2) + (2*d+1)) + 1 by omega]
    cases h : P q (heads t) with
    | halt accept sign => simp [TeamStack.paths, code, h, negative, paths]
    | one c =>
      simp only [TeamStack.paths, code, h, paths]
      exact (signedPaths_runs (sweep_run P c t) _).trans (ih _ _)
    | two low high =>
      simp only [TeamStack.paths, code, h, paths]
      exact congrArg₂ Int.add ((signedPaths_runs (sweep_run P low t) _).trans (ih _ _))
        ((signedPaths_runs (sweep_run P high t) _).trans (ih _ _))

end TeamPrivateTape

end BorderVNP
end Computability
end OAI
