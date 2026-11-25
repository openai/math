import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode
import OAI.Computability.NearSquareRoot.ShortWordSpace
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Physical preparation of the generator's unary input

The two-tape adapter copies the index marks and appends the encoded positive
terminator. A reverse scan on the read-only source restores both heads to
their initial positions. The source word may start at any absolute address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Input
open IntegerMultiplication TM

inductive Control where
  | copy | last | turn | rewind | done
  deriving DecidableEq

instance : Finite Control := Finite.of_injective
  (fun q : Control => match q with
    | .copy => (0 : Fin 5) | .last => 1 | .turn => 2 | .rewind => 3 | .done => 4)
  (by intro x y h; cases x <;> cases y <;> simp_all)

variable {D : Type}

def word (cons one : D) (j : ℕ) := List.replicate j cons ++ [one,cons]

theorem trList_input (j : ℕ) :
    Turing.PartrecToTM2.trList (unaryInput j) =
      word Turing.PartrecToTM2.Γ'.cons .bit1 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show unaryInput (j+1) = 0 :: unaryInput j by simp [unaryInput,List.replicate_succ]]
    simp [ih,word,List.replicate_succ]

theorem map_trList_input (f : Turing.PartrecToTM2.Γ' → D) (j : ℕ) :
    (Turing.PartrecToTM2.trList (unaryInput j)).map f = word (f .cons) (f .bit1) j := by
  simp [trList_input,word]

private def issue (r : Bool → D) (q : Control) (a b : Move) (v : D) :
    Option (Control × (Bool → D × Move)) :=
  some (q,fun | false => (r false,a) | true => (v,b))

def rule [DecidableEq D] (mark cons one : D) : Rule D Control Bool
  | .copy, r => if r false = mark then issue r .copy .right .right cons
                 else issue r .last .stay .right one
  | .last, r => issue r .turn .stay .left cons
  | .turn, r => issue r .rewind .left .left (r true)
  | .rewind, r => if r false = mark then issue r .rewind .left .left (r true)
                   else issue r .done .right .right (r true)
  | .done, _ => none

/-- Source head at the front of the unary input, translated to an arbitrary address. -/
def source (blank mark : D) (H : ℤ) (j : ℕ) : Tape D :=
  ⟨H,(Tape.loaded blank (List.replicate j mark)).view⟩

def pair (q : Control) (s d : Tape D) : Config D Control Bool :=
  ⟨q,fun | false => s | true => d⟩

private def atOffset (H q : ℤ) (f : ℤ → D) : Tape D :=
  ⟨H+q,fun k => f (q+k)⟩

private theorem move_at (H p : ℤ) (f : ℤ → D) (m : Move) :
    (atOffset H p f).apply (f p,m) = atOffset H (p+m.shift) f := by
  simp only [atOffset,Tape.apply,add_assoc,Tape.mk.injEq,true_and]
  funext k
  split
  · rename_i e; congr 1; omega
  · congr 1; omega

private def partialWord (blank : D) (w : List D) (k : ℕ) (z : ℤ) :=
  if z < k then (Tape.loaded blank w).view z else blank

private theorem write_at (blank : D) (w : List D) (p : ℕ) (m : Move) :
    (atOffset 0 p (partialWord blank w p)).apply ((Tape.loaded blank w).view p,m) =
      atOffset 0 (p+m.shift) (partialWord blank w (p+1)) := by
  simp only [atOffset,Tape.apply,zero_add,Tape.mk.injEq,true_and]
  funext k
  simp only [partialWord,Nat.cast_add,Nat.cast_one]
  by_cases h : k+m.shift = 0
  · rw [ite_eq_left h,show (p:ℤ)+m.shift+k=p by omega,ite_eq_left (by omega)]
  · rw [ite_eq_right h,show (p:ℤ)+(k+m.shift)=p+m.shift+k by omega]
    by_cases l : (p:ℤ)+m.shift+k < p
    · rw [ite_eq_left l,ite_eq_left (by omega)]
    · rw [ite_eq_right l,ite_eq_right (by omega)]

private theorem partial_full (blank : D) (w : List D) :
    partialWord blank w w.length = (Tape.loaded blank w).view := by
  funext z
  unfold partialWord
  split
  · rfl
  · rename_i h
    cases z with
    | negSucc n => omega
    | ofNat n =>
      change ¬(n:ℤ) < w.length at h
      have h' : w.length ≤ n := by omega
      simp [Tape.loaded,List.getElem?_eq_none h']

private theorem partial_empty (blank : D) (w : List D) :
    partialWord blank w 0 = (Tape.loaded blank []).view := by
  funext z
  cases z with
  | negSucc n => simp [partialWord,Tape.loaded]
  | ofNat n => simp [partialWord,Tape.loaded]

variable (blank mark cons one : D) (H : ℤ) (j : ℕ)
private abbrev src (q : ℤ) := atOffset H q (source blank mark H j).view
private abbrev dst (q : ℤ) (k : ℕ) := atOffset 0 q (partialWord blank (word cons one j) k)
private abbrev endDst (q : ℤ) := atOffset 0 q (Tape.loaded blank (word cons one j)).view

private theorem read_mark (k : ℕ) (hk : k < j) :
    (source blank mark H j).view k = mark := by
  simp [source,Tape.loaded,List.getElem?_replicate,hk]

private theorem read_blank :
    (source blank mark H j).view j = blank := by
  simp [source,Tape.loaded,List.getElem?_replicate]

private theorem read_cons (k : ℕ) (hk : k < j) :
    (Tape.loaded blank (word cons one j)).view k = cons := by
  simp [word,Tape.loaded,List.getElem?_append,
    List.getElem?_replicate,hk]

private theorem read_one :
    (Tape.loaded blank (word cons one j)).view j = one := by
  simp [word,Tape.loaded]

private theorem read_last :
    (Tape.loaded blank (word cons one j)).view (j+1 : ℕ) = cons := by
  change ((List.replicate j cons ++ [one,cons])[j+1]?).getD blank = cons
  simp

variable [DecidableEq D]
local notation "M" => rule mark cons one
private theorem step {q q' : Control} {s d s' d' : Tape D} {ms md : Move} {v : D}
    (h : M q (fun i => ((pair q s d).tape i).view 0) =
      issue (fun i => ((pair q s d).tape i).view 0) q' ms md v)
    (hs : s.apply (s.view 0,ms) = s') (hd : d.apply (v,md) = d') :
    advance M (pair q s d) = some (pair q' s' d') := by
  unfold advance
  rw [show (pair q s d).pc=q from rfl,h]
  simp only [issue,Option.map_some,Option.some.injEq,pair,Config.mk.injEq,true_and]
  funext i
  cases i <;> assumption

private theorem forward (k : ℕ) (hk : k < j) :
    advance M (pair .copy (src blank mark H j k) (dst blank cons one j k k)) =
      some (pair .copy (src blank mark H j (k+1 : ℕ)) (dst blank cons one j (k+1 : ℕ) (k+1))) := by
  apply step (ms := .right) (md := .right) (v := cons)
  · simp only [rule,pair,atOffset,add_zero,read_mark blank mark H j k hk,ite_true]
  · simpa [src,atOffset,Move.shift] using move_at H k (source blank mark H j).view .right
  · simpa only [read_cons blank cons one j k hk,Move.shift,Nat.cast_add,Nat.cast_one]
      using write_at blank (word cons one j) k .right

private theorem forward_scan (k : ℕ) (hk : k ≤ j) :
    Trace (advance M) (pair .copy (src blank mark H j 0) (dst blank cons one j 0 0)) k
      (pair .copy (src blank mark H j k) (dst blank cons one j k k)) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    exact (ih (by omega)).trans (.single (forward blank mark cons one H j k hk))

private theorem back_step (k : ℕ) (hk : k < j) :
    advance M (pair .rewind (src blank mark H j k) (endDst blank cons one j k)) =
      some (pair .rewind (src blank mark H j ((k:ℤ)-1)) (endDst blank cons one j ((k:ℤ)-1))) := by
  apply step (ms := .left) (md := .left) (v := (endDst blank cons one j k).view 0)
  · simp only [rule,pair,atOffset,add_zero,read_mark blank mark H j k hk,ite_true]
  · simpa [src,atOffset,Move.shift,sub_eq_add_neg] using move_at H k (source blank mark H j).view .left
  · simpa [endDst,atOffset,Move.shift,sub_eq_add_neg] using
      move_at 0 k (Tape.loaded blank (word cons one j)).view .left

private theorem back_scan (k : ℕ) (hk : k ≤ j) :
    Trace (advance M) (pair .rewind (src blank mark H j ((k:ℤ)-1)) (endDst blank cons one j ((k:ℤ)-1))) k
      (pair .rewind (src blank mark H j (-1)) (endDst blank cons one j (-1))) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    rw [show ((k+1:ℕ):ℤ)-1 = (k:ℤ) by omega]
    simpa only [Nat.one_add] using Trace.cons (back_step blank mark cons one H j k hk) (ih (by omega))

private theorem delimiter (distinct : blank ≠ mark) :
    advance M (pair .copy (src blank mark H j j) (dst blank cons one j j j)) =
      some (pair .last (src blank mark H j j) (dst blank cons one j (j+1 : ℕ) (j+1))) := by
  apply step (ms := .stay) (md := .right) (v := one)
  · simp only [rule,pair,atOffset,add_zero,read_blank blank mark H j,distinct,ite_false]
  · simpa [src,atOffset,Move.shift] using move_at H j (source blank mark H j).view .stay
  · simpa only [read_one blank cons one j,Move.shift,Nat.cast_add,Nat.cast_one]
      using write_at blank (word cons one j) j .right

private theorem trailer :
    advance M (pair .last (src blank mark H j j) (dst blank cons one j (j+1 : ℕ) (j+1))) =
      some (pair .turn (src blank mark H j j) (endDst blank cons one j j)) := by
  apply step (ms := .stay) (md := .left) (v := cons)
  · rfl
  · simpa [src,atOffset,Move.shift] using move_at H j (source blank mark H j).view .stay
  · have sw : (word cons one j).length = j+1+1 := by simp [word]
    have w := write_at blank (word cons one j) (j+1) .left
    rw [read_last blank cons one j,← sw,partial_full] at w
    simpa [Move.shift] using w

private theorem turn :
    advance M (pair .turn (src blank mark H j j) (endDst blank cons one j j)) =
      some (pair .rewind (src blank mark H j ((j:ℤ)-1)) (endDst blank cons one j ((j:ℤ)-1))) := by
  apply step (ms := .left) (md := .left) (v := (endDst blank cons one j j).view 0)
  · rfl
  · simpa [src,atOffset,Move.shift,sub_eq_add_neg] using move_at H j (source blank mark H j).view .left
  · simpa [endDst,atOffset,Move.shift,sub_eq_add_neg] using
      move_at 0 j (Tape.loaded blank (word cons one j)).view .left

private theorem stop (distinct : blank ≠ mark) :
    advance M (pair .rewind (src blank mark H j (-1)) (endDst blank cons one j (-1))) =
      some (pair .done (src blank mark H j 0) (endDst blank cons one j 0)) := by
  apply step (ms := .right) (md := .right) (v := (endDst blank cons one j (-1)).view 0)
  · have e : (source blank mark H j).view (-1) = blank := rfl
    simp only [rule,pair,atOffset,add_zero,e,distinct,ite_false]
  · simpa [src,atOffset,Move.shift] using move_at H (-1) (source blank mark H j).view .right
  · simpa [endDst,atOffset,Move.shift] using
      move_at 0 (-1) (Tape.loaded blank (word cons one j)).view .right

/-- The index and generator heads return exactly to their initial locations. -/
theorem run (distinct : blank ≠ mark) :
    Trace (advance M) (pair .copy (source blank mark H j) (Tape.loaded blank [])) (2*j+4)
      (pair .done (source blank mark H j) (Tape.loaded blank (word cons one j))) := by
  have full := (forward_scan blank mark cons one H j j (by rfl)).trans
    ((Trace.single (delimiter blank mark cons one H j distinct)).trans
    ((Trace.single (trailer blank mark cons one H j)).trans
    ((Trace.single (turn blank mark cons one H j)).trans
    ((back_scan blank mark cons one H j j (by rfl)).trans
      (Trace.single (stop blank mark cons one H j distinct))))))
  have start : src blank mark H j 0 = source blank mark H j := by
    simp only [src,atOffset,add_zero,zero_add,source]
  have empty : dst blank cons one j 0 0 = Tape.loaded blank [] := by
    simp [dst,partial_empty,atOffset,Tape.loaded]
  have out : endDst blank cons one j 0 = Tape.loaded blank (word cons one j) := by
    simp [endDst,atOffset,Tape.loaded]
  rw [start,empty,out] at full
  convert full using 1
  omega

theorem halted :
    advance M (pair .done (source blank mark H j) (Tape.loaded blank (word cons one j))) = none := rfl

/-- The total number of visited cells on both tapes is linear in the unary input,
independently of the absolute address of its first mark. -/
theorem space :
    VisitsAtMost M (pair .copy (source blank mark H j) (Tape.loaded blank [])) (2*j+4) (8*j+18) := by
  let x := pair .copy (source blank mark H j) (Tape.loaded blank [])
  let t := 2*j+4
  let lo (i : Bool) := (x.tape i).pos - (t:ℤ)
  let hi (i : Bool) := (x.tape i).pos + (t:ℤ)
  have hs := visitsAtMost_of_tape_fences (m := M) (init := x) (steps := t) lo hi (by
    intro u hu c run i
    have e := head_excursion run i
    dsimp [lo,hi]
    omega)
  convert hs using 1
  simp [lo,hi,t]
  omega

end Generator.Input

end NearSquareRoot
end Computability
end OAI
