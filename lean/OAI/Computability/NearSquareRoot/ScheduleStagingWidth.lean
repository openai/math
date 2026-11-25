import OAI.Computability.NearSquareRoot.ScheduleStagingMarks
import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeTape
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-! # Generating the fixed fence width from literal input

The width tape receives a block before scanning and a further block for every
bit of the first operand. Its delimiter therefore falls at the exact common
radius. The output head returns to zero while the source stays on the public
separator, preserving all source symbols.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingWidth

open IntegerMultiplication TM Code Bits CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open ChunkControl (Driver)
open StagingSerialize (content put read raw)

def block (C : ℕ) := 4*(C+50)

inductive Phase (C : ℕ)
  | emit (j : Fin (block C)) | scan | back | done
  deriving Fintype, DecidableEq

def emitAt (C j : ℕ) : Phase C := atIndex (block C) .emit .scan j
def start (C : ℕ) : Phase C := emitAt C 0

def token (d : Driver) : StagingControl.Letter d := some (.inl (.bit false))
def delimiter (d : Driver) : StagingControl.Letter d := some (.inl .sep)
def first (d : Driver) (C n : ℕ) := List.replicate (StagingProtection.Rpub C n) (token d)

theorem first_length (d : Driver) (C n : ℕ) :
    (first d C n).length = StagingProtection.Rpub C n := by simp [first]
theorem first_delim (d : Driver) (C n : ℕ) : delimiter d ∉ first d C n := by simp [first,token,delimiter]
theorem first_blank (d : Driver) (C n : ℕ) : none ∉ first d C n := by simp [first,token]

def rule (d : Driver) (C : ℕ) : Rule (StagingProtection.Cell d) (Phase C) Bool := fun q h =>
  let keep (q' : Phase C) (s o : Move) := some (q',pair (h false,s) (h true,o))
  match q with
  | .emit j => some (emitAt C (j.val+1),pair (h false,.stay) (put d (.bit false),.right))
  | .scan => match read d (h false) with
    | some (.bit _) => keep (start C) .right .stay
    | _ => some (.back,pair (h false,.stay) (put d .sep,.stay))
  | .back => if (read d (h true)).isSome then keep .back .stay .left else keep .done .stay .right
  | .done => none

def initial (d : Driver) (C : ℕ) (x y : Word) : Config (StagingProtection.Cell d) (Phase C) Bool :=
  ⟨start C, StagingSerialize.tapes d x y []⟩

def widthTape (d : Driver) (C n : ℕ) :=
  Tape.loaded (StagingMarks.plain d none) ((first d C n ++ [delimiter d]).map (StagingMarks.plain d))

def doneConfig (d : Driver) (C : ℕ) (x y : Word) : Config (StagingProtection.Cell d) (Phase C) Bool :=
  ⟨.done,pair (Reset.atHead x.length (content d (raw x y))) (widthTape d C x.length)⟩

private def zeros (n : ℕ) : List Ltr := List.replicate n (.bit false)

private theorem appended (d : Driver) (j : ℕ) :
    Function.update (content d (zeros j)) (j:ℤ) (put d (.bit false)) = content d (zeros (j+1)) := by
  simpa only [zeros,List.length_replicate,List.replicate_succ'] using
    StagingSerialize.content_snoc d (zeros j) (.bit false)

private theorem emit (d : Driver) (C : ℕ) (s : List Ltr) (p : ℤ) (a : ℕ) :
    Trace (advance (rule d C)) (cfg (start C) p a (content d s) (content d (zeros a)))
      (block C) (cfg .scan p (a+block C : ℕ) (content d s) (content d (zeros (a+block C)))) := by
  let F (j : ℕ) := cfg (emitAt C j) p (a+j : ℕ) (content d s) (content d (zeros (a+j)))
  have hist := Expand.steps (rule d C) F (block C) fun j hj => by
    have pc : emitAt C j = .emit ⟨j,hj⟩ := dite_eq_left hj
    have one := Expand.step (rule d C) (emitAt C j) (emitAt C (j+1)) p (a+j : ℕ)
      (content d s) (content d (zeros (a+j))) (put d (.bit false)) .stay .right (by rw [pc]; rfl)
    rw [appended] at one
    simpa only [F,Move.shift,add_zero,Nat.cast_add,Nat.cast_one,add_assoc] using one
  have term : emitAt C (block C) = .scan := dite_eq_right (lt_irrefl _)
  simpa only [F,start,term,Nat.add_zero] using hist

private theorem forward (d : Driver) (C : ℕ) (x y : Word) (j : ℕ) (hj : j ≤ x.length) :
    let count := block C * (j+1)
    Trace (advance (rule d C)) (initial d C x y) (block C+(block C+1)*j)
      (cfg .scan j count (content d (raw x y)) (content d (zeros count))) := by
  dsimp only
  induction j with
  | zero =>
    have first := emit d C (raw x y) 0 0
    simpa only [initial,StagingSerialize.tapes,cfg,zeros,List.replicate_zero,
      StagingSerialize.at_zero,List.map_nil,Nat.cast_zero,Nat.zero_add,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
      using first
  | succ j ih =>
    have h := ih (by omega)
    have bound : j < x.length := by omega
    let count := block C*(j+1)
    have get : content d (raw x y) j = put d (.bit x[j]) := by
      simp [StagingSerialize.content_at,raw,
        List.getElem?_append_left (by simpa using bound : j < (x.map Ltr.bit).length),
        List.getElem?_eq_getElem bound]
    have shift := Expand.move (rule d C) .scan (start C) j count
      (content d (raw x y)) (content d (zeros count)) .right .stay (by simp [rule,pair,get])
    have extra := emit d C (raw x y) (↑j+1) count
    have one := (Trace.single (by simpa only [Move.shift,add_zero] using shift :
      advance (rule d C) _ = some (cfg (start C) (↑j+1) count (content d (raw x y)) (content d (zeros count))))).trans extra
    convert h.trans one using 1
    all_goals simp only [count,Nat.cast_succ,Nat.mul_succ]
    all_goals omega

private theorem rewind (d : Driver) (C : ℕ) (s out : List Ltr) (p : ℤ) (j : ℕ) (hj : j ≤ out.length) :
    Trace (advance (rule d C)) (cfg .back p ((j : ℤ)-1) (content d s) (content d out)) (j+1)
      (cfg .done p 0 (content d s) (content d out)) := by
  induction j with
  | zero =>
    have step := Expand.move (rule d C) .back .done p (-1) (content d s) (content d out)
      .stay .right (by simp [rule,pair])
    simpa [Move.shift] using Trace.single step
  | succ j ih =>
    have step := Expand.move (rule d C) .back .back p j (content d s) (content d out)
      .stay .left (by simp [rule,pair,StagingSerialize.content_get d out j (by omega)])
    have one := Trace.single (by simpa only [Move.shift,add_zero,sub_eq_add_neg] using step :
      advance (rule d C) _ = some (cfg .back p ((j:ℤ)-1) (content d s) (content d out)))
    simpa [Nat.add_comm 1] using one.trans (ih (by omega))

/-- The physical clock includes writing and rewinding every radius cell.
The parked source head finishes exactly on the original separator. -/
theorem run (d : Driver) (C : ℕ) (x y : Word) :
    let R := StagingProtection.Rpub C x.length
    Trace (advance (rule d C)) (initial d C x y) (2*R+x.length+3) (doneConfig d C x y) ∧
      advance (rule d C) (doneConfig d C x y) = none := by
  let R := StagingProtection.Rpub C x.length
  let s := raw x y
  let out := zeros R ++ [.sep]
  have go := forward d C x y x.length le_rfl
  have fin : content d s x.length = put d .sep := by
    simpa only [s,raw,List.length_map] using StagingSerialize.content_next d (x.map Ltr.bit) (y.map Ltr.bit) .sep
  have mark := Expand.step (rule d C) .scan .back x.length R (content d s) (content d (zeros R))
    (put d .sep) .stay .stay (by simp [rule,pair,fin])
  have upd := StagingSerialize.content_snoc d (zeros R) .sep
  simp only [zeros,List.length_replicate] at upd
  change Function.update (content d (zeros R)) (R:ℤ) (put d .sep) = content d out at upd
  rw [upd] at mark
  have marked := Trace.single (by simpa only [Move.shift,add_zero] using mark :
    advance (rule d C) _ = some (cfg .back x.length R (content d s) (content d out)))
  have back := rewind d C s out x.length out.length le_rfl
  have len : out.length = R+1 := by simp [out,zeros]
  rw [len] at back
  simp only [Nat.cast_succ,add_sub_cancel_right] at back
  have all := (go.trans marked).trans back
  have dst : Reset.atHead 0 (content d out) = widthTape d C x.length := by
    rw [StagingSerialize.at_zero]
    simp [out,zeros,widthTape,first,List.map_replicate]
    rfl
  have endpoint : cfg (.done : Phase C) x.length 0 (content d s) (content d out) = doneConfig d C x y := by
    simp only [cfg,dst,doneConfig,s]
  rw [endpoint] at all
  refine ⟨?_,rfl⟩
  convert all using 1
  change 2*(block C*(x.length+1))+x.length+3 = _
  change _ = block C+(block C+1)*x.length+1+(block C*(x.length+1)+1+1)
  ring

theorem clock_le (C n : ℕ) :
    2*StagingProtection.Rpub C n+n+3 ≤ (2*block C+3)*(n+1) := by
  change 2*(block C*(n+1))+n+3 ≤ _
  nlinarith

theorem prefix_within (d : Driver) (C : ℕ) (x y : Word) {j : ℕ} {z}
    (pref : Trace (advance (rule d C)) (initial d C x y) j z) (i : Bool) :
    let bound := (2*block C+3)*(x.length+1)
    (-(bound:ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ bound) := by
  obtain ⟨tr,stop⟩ := run d C x y
  have time := (Uniform.before_halt tr stop pref).trans (clock_le C x.length)
  have pos : ((initial d C x y).tape i).pos = 0 := by cases i <;> rfl
  obtain ⟨lo,hi⟩ := head_excursion pref i
  rw [pos] at lo hi
  dsimp only
  omega

theorem visited (d : Driver) (C budget : ℕ) (x y : Word) :
    VisitsAtMost (rule d C) (initial d C x y) budget
      ((8*block C+14)*(x.length+1)) := by
  let bound := (2*block C+3)*(x.length+1)
  have space := visitsAtMost_of_common_fence (m:=rule d C) (init:=initial d C x y) (steps:=budget)
    (-(bound:ℤ)) (bound:ℤ) (fun _ _ _ sub i => prefix_within d C x y sub i)
  obtain ⟨cells,h,all⟩ := space
  refine ⟨cells,h.trans ?_,all⟩
  rw [Fintype.card_bool,show ((bound:ℤ)+1-(-(bound:ℤ))).toNat=2*bound+1 by omega]
  dsimp only [bound]
  nlinarith

end StagingWidth

end NearSquareRoot
end Computability
end OAI
