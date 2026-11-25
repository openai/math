import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# A single finite interpreter for programs with arbitrary finite control

The interpreted alphabet and number of data heads are common to all programs.
Two extra tapes contain identical transition lists. One head locates a row,
while the other is parked at the origin. A selected branch contains its output
moves and a unary destination row number. Reading these ticks scans the other
copy up to its destination; rewinding the used copy exchanges the two roles.
The transition function itself is independent of the table and state count.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal

open IntegerMultiplication
variable {A I : Type}

/-- Symbols in both read-only program copies. -/
inductive Tag (A I : Type) where
  | origin
  | row
  | branch (read : I → A) (op : Option (I → A × TM.Move))
  | tick
  | endCode

noncomputable instance [Finite A] [Finite I] : Finite (Tag A I) := by
  let _ : Finite TM.Move := Finite.of_injective
    (fun m : TM.Move => match m with | .left => (0 : Fin 3) | .stay => 1 | .right => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)
  let f : Tag A I → Fin 4 ⊕ ((I → A) × Option (I → A × TM.Move))
    | .origin => .inl 0
    | .row => .inl 1
    | .tick => .inl 2
    | .endCode => .inl 3
    | .branch r o => .inr (r,o)
  exact Finite.of_injective f (by intro a b h; cases a <;> cases b <;> simp_all [f])

/-- Finite control of the two-copy interpreter. -/
inductive Phase
  | seek | dest | skip | rewind
  deriving DecidableEq

instance : Finite Phase := Finite.of_injective
  (fun p : Phase => match p with | .seek => (0 : Fin 4) | .dest => 1 | .skip => 2 | .rewind => 3)
  (by intro a b h; cases a <;> cases b <;> simp_all)

abbrev Letter (A I : Type) := A ⊕ Tag A I
abbrev Index (I : Type) := I ⊕ Bool
abbrev PC := Bool × Phase

/-- A ROM pointer addresses a literal physical cell. -/
def atCell (s : ℤ → Tag A I) (p : ℤ) : TM.Tape (Letter A I) :=
  ⟨p, fun d => .inr (s (p+d))⟩

def dataCell (t : TM.Tape A) : TM.Tape (Letter A I) :=
  ⟨t.pos, fun d => .inl (t.view d)⟩

/-- The active program copy is selected by `side`. Both copies persist. -/
def conf (s : ℤ → Tag A I) (d : I → TM.Tape A)
    (side : Bool) (phase : Phase) (p q : ℤ) :
    TM.Config (Letter A I) PC (Index I) :=
  ⟨(side,phase), fun
    | .inl i => dataCell (d i)
    | .inr b => atCell s (if b = side then p else q)⟩

def readData (blank : A) (v : Index I → Letter A I) (i : I) :=
  match v (.inl i) with
  | .inl a => a
  | .inr _ => blank

def tagAt (v : Index I → Letter A I) (b : Bool) : Tag A I :=
  match v (.inr b) with
  | .inl _ => .endCode
  | .inr t => t

def issue (v : Index I → Letter A I) (side : Bool) (pc : PC)
    (a b : TM.Move) (write : Option (I → A × TM.Move)) :
    Option (PC × (Index I → Letter A I × TM.Move)) :=
  some (pc, fun
    | .inl i =>
      match write with
      | none => (v (.inl i), .stay)
      | some o => (.inl (o i).1, (o i).2)
    | .inr j => (v (.inr j), if j = side then a else b))

/-- The only comparison of head symbols tests equality in the fixed finite read tuple. -/
noncomputable def rule [Finite I] [Finite A] (blank : A) :
    TM.Rule (Letter A I) PC (Index I) := by
  classical
  exact fun (side,phase) v =>
    let send := issue v side
    match phase with
    | .seek =>
      match tagAt v side with
      | .branch r op =>
        if r = readData blank v then
          match op with
          | none => none
          | some o => send (side,.dest) .right .right (some o)
        else send (side,.seek) .right .stay none
      | _ => send (side,.seek) .right .stay none
    | .dest =>
      match tagAt v side with
      | .tick => send (side,.skip) .stay .right none
      | _ => send (side,.rewind) .stay .stay none
    | .skip =>
      match tagAt v (!side) with
      | .row => send (side,.dest) .right .stay none
      | _ => send (side,.skip) .stay .right none
    | .rewind =>
      match tagAt v side with
      | .origin => send (!side,.seek) .stay .stay none
      | _ => send (side,.rewind) .left .stay none



private theorem rom_move (s : ℤ → Tag A I) (p : ℤ) (m : TM.Move) :
    (atCell s p).apply ((atCell s p).view 0, m) = atCell s (p + m.shift) := by
  simp only [atCell, TM.Tape.apply, add_zero, TM.Tape.mk.injEq, true_and]
  funext d
  split <;> rename_i h
  · rw [show p + m.shift + d = p by omega]
  · rw [show p + m.shift + d = p + (d + m.shift) by omega]

private theorem data_write (t : TM.Tape A) (a : A) (m : TM.Move) :
    (dataCell (I := I) t).apply (.inl a, m) = dataCell (t.apply (a,m)) := by
  simp only [dataCell, TM.Tape.apply, TM.Tape.mk.injEq, true_and]
  funext d
  split <;> rfl

private theorem data_stay (t : TM.Tape A) :
    (dataCell (I := I) t).apply ((dataCell t).view 0, .stay) = dataCell t := by
  simp only [dataCell, TM.Tape.apply, TM.Move.shift, add_zero, TM.Tape.mk.injEq, true_and]
  funext d
  split <;> simp_all

private def updated (d : I → TM.Tape A) (op : Option (I → A × TM.Move)) : I → TM.Tape A :=
  match op with | none => d | some o => fun i => (d i).apply (o i)

private def heads (c : TM.Config (Letter A I) PC (Index I)) :=
  fun i => (c.tape i).view 0

@[simp] private theorem read_conf (blank : A) (s : ℤ → Tag A I) (d : I → TM.Tape A)
    (b : Bool) (f : Phase) (p q : ℤ) :
    readData blank (heads (conf s d b f p q)) = fun i => (d i).view 0 := rfl

@[simp] private theorem tag_conf (s : ℤ → Tag A I) (d : I → TM.Tape A)
    (b j : Bool) (f : Phase) (p q : ℤ) :
    tagAt (heads (conf s d b f p q)) j = s (if j = b then p else q) := by
  simp [tagAt, heads, conf, atCell]

private theorem advance_issue {m : TM.Rule (Letter A I) PC (Index I)}
    (s : ℤ → Tag A I) (d : I → TM.Tape A) (b : Bool) (f f' : Phase) (p q : ℤ)
    (mp mq : TM.Move) (op : Option (I → A × TM.Move))
    (h : m (b,f) (heads (conf s d b f p q)) =
      issue (heads (conf s d b f p q)) b (b,f') mp mq op) :
    TM.advance m (conf s d b f p q) =
      some (conf s (updated d op) b f' (p+mp.shift) (q+mq.shift)) := by
  unfold TM.advance
  change Option.map _ (m (b,f) (heads _)) = _
  rw [h]
  simp only [issue, Option.map_some, Option.some.injEq]
  apply congrArg (TM.Config.mk (b,f'))
  funext i
  cases i with
  | inl i =>
    cases op with
    | none => exact data_stay (d i)
    | some o => exact data_write (d i) (o i).1 (o i).2
  | inr j =>
    by_cases he : j = b
    · subst j; simpa [heads, conf] using rom_move s p mp
    · simpa [heads, conf, he] using rom_move s q mq

/-- A tag unequal to the selected read tuple can be skipped by one transition. -/
def branchReads (v : I → A) : Tag A I → Prop
  | .branch r _ => r = v
  | _ => False

section
variable [Finite A] [Finite I] (blank : A) (s : ℤ → Tag A I) (d : I → TM.Tape A)
    (b : Bool) (p q : ℤ)

theorem seek_next (h : ¬ branchReads (fun i => (d i).view 0) (s p)) :
    TM.advance (rule blank) (conf s d b .seek p q) =
      some (conf s d b .seek (p+1) q) := by
  have := advance_issue (m := rule blank) s d b .seek .seek p q .right .stay none (by
    simp only [rule, tag_conf, ite_true, read_conf]
    cases he : s p <;> simp_all [branchReads])
  simpa [updated, TM.Move.shift] using this

theorem seek_apply {op : I → A × TM.Move}
    (h : s p = .branch (fun i => (d i).view 0) (some op)) :
    TM.advance (rule blank) (conf s d b .seek p q) =
      some (conf s (fun i => (d i).apply (op i)) b .dest (p+1) (q+1)) := by
  exact advance_issue (m := rule blank) s d b .seek .dest p q .right .right (some op) (by
    simp [rule, h])

theorem seek_halt (h : s p = .branch (fun i => (d i).view 0) none) :
    TM.advance (rule blank) (conf s d b .seek p q) = none := by
  unfold TM.advance
  change Option.map _ (rule blank (b,.seek) (heads _)) = _
  simp [rule, h]

theorem dest_tick (h : s p = .tick) :
    TM.advance (rule blank) (conf s d b .dest p q) =
      some (conf s d b .skip p (q+1)) := by
  have := advance_issue (m := rule blank) s d b .dest .skip p q .stay .right none (by
    simp [rule, h])
  simpa [updated, TM.Move.shift] using this

theorem dest_end (h : s p ≠ .tick) :
    TM.advance (rule blank) (conf s d b .dest p q) =
      some (conf s d b .rewind p q) := by
  have := advance_issue (m := rule blank) s d b .dest .rewind p q .stay .stay none (by
    simp only [rule, tag_conf, ite_true])
  simpa [updated, TM.Move.shift] using this

theorem skip_next (h : s q ≠ .row) :
    TM.advance (rule blank) (conf s d b .skip p q) =
      some (conf s d b .skip p (q+1)) := by
  have := advance_issue (m := rule blank) s d b .skip .skip p q .stay .right none (by
    simp only [rule, tag_conf, Bool.not_eq_self, ite_false])
  simpa [updated, TM.Move.shift] using this

theorem skip_row (h : s q = .row) :
    TM.advance (rule blank) (conf s d b .skip p q) =
      some (conf s d b .dest (p+1) q) := by
  have := advance_issue (m := rule blank) s d b .skip .dest p q .right .stay none (by
    simp [rule, h])
  simpa [updated, TM.Move.shift] using this

theorem rewind_left (h : s p ≠ .origin) :
    TM.advance (rule blank) (conf s d b .rewind p q) =
      some (conf s d b .rewind (p-1) q) := by
  have := advance_issue (m := rule blank) s d b .rewind .rewind p q .left .stay none (by
    simp only [rule, tag_conf, ite_true])
  simpa [updated, TM.Move.shift, sub_eq_add_neg] using this

theorem rewind_swap (h : s p = .origin) :
    TM.advance (rule blank) (conf s d b .rewind p q) =
      some (conf s d (!b) .seek q p) := by
  unfold TM.advance
  change Option.map _ (rule blank (b,.rewind) (heads _)) = _
  simp only [rule, tag_conf, ite_true, h, issue, Option.map_some, Option.some.injEq]
  apply congrArg (TM.Config.mk (A := Letter A I) (I := Index I) ((!b,.seek) : PC))
  funext i
  cases i with
  | inl i => exact data_stay (d i)
  | inr j =>
    cases b <;> cases j <;> simpa [heads, conf, TM.Move.shift] using rom_move s _ .stay

end
end Universal

end NearSquareRoot
end Computability
end OAI
