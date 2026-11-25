import OAI.Computability.NearSquareRoot.CommonAlphabetFold
import OAI.Computability.NearSquareRoot.ScheduleInterpreterReset
import Mathlib.Tactic.DeriveFintype

/-! # Following the absolute distance of a head with one physical tape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM
variable {A Q I : Type}

inductive Phase (Q : Type)
  | boot | run (q : Q) (neg : Bool) | rewind (neg : Bool) | done
  deriving Fintype

def banks {X : Type} (old : I → X) (extra : X) : Option I → X
  | none => extra | some i => old i

def mark (blank marker : A) (p : ℤ) := if p = 0 then marker else blank

def counter (blank marker : A) (n : ℕ) : Tape A := Reset.atHead n (mark blank marker)

def initial (x : Config A Q I) (blank : A) : Config A (Phase Q) (Option I) :=
  ⟨.boot, banks x.tape (Tape.loaded blank [])⟩

def running (out : I) (blank marker : A) (neg : Bool) (x : Config A Q I) :
    Config A (Phase Q) (Option I) :=
  ⟨.run x.pc neg,banks x.tape (counter blank marker (x.tape out).pos.natAbs)⟩

def rule [DecidableEq A] [DecidableEq I] (out : I) (blank marker : A) (entry : Q)
    (m : Rule A Q I) : Rule A (Phase Q) (Option I) := fun q h =>
  let stationary := fun i => (h (some i),Move.stay)
  let here := decide (h none = marker)
  match q with
  | .boot => some (.run entry false, banks stationary (marker,.stay))
  | .run old neg => match m old (fun i => h (some i)) with
    | none => some (.rewind neg, banks stationary (h none,.stay))
    | some (q',o) =>
      let d := (o out).2
      some (.run q' (foldSign here neg d), banks o (h none,foldMove here neg d))
  | .rewind neg =>
    if here then some (.done, banks stationary (blank,.stay))
    else some (.rewind neg, banks
      (fun i => (h (some i), if i=out then toward neg else .stay)) (h none,.left))
  | .done => none

theorem asAtHead (t : Tape A) : Reset.atHead t.pos t.absolute = t := by
  cases t with
  | mk p f => simp [Reset.atHead, Tape.absolute]

theorem stay (t : Tape A) : t.apply (t.view 0,.stay) = t := by
  generalize h : t.view 0 = v
  rw [← asAtHead t] at h ⊢
  simp only [Reset.atHead,add_zero] at h
  rw [← h, Reset.atHead_apply, Function.update_eq_self]
  simp [Move.shift]

theorem here (blank marker : A) (hne : blank ≠ marker) (p : ℤ) :
    (counter blank marker p.natAbs).view 0 = marker ↔ p = 0 := by
  by_cases h : p=0 <;> simp [counter,Reset.atHead,mark,h,hne]

theorem start [DecidableEq A] [DecidableEq I] (out : I) (blank marker : A)
    (m : Rule A Q I) (x : Config A Q I) (atZero : (x.tape out).pos = 0) :
    advance (rule out blank marker x.pc m) (initial x blank) =
      some (running out blank marker false x) := by
  change some _ = some _
  congr 1
  dsimp only [running,initial]
  rw [Config.mk.injEq]
  refine ⟨rfl,?_⟩
  funext i
  cases i with
  | some i => exact stay _
  | none =>
    change (Tape.loaded blank []).apply (marker,.stay) = counter blank marker (x.tape out).pos.natAbs
    rw [atZero]
    simp only [counter, Reset.atHead, Tape.loaded, Tape.apply, Move.shift, Int.natAbs_zero,
      Nat.cast_zero, add_zero, zero_add, Tape.mk.injEq, true_and]
    funext p
    cases p <;> simp [mark]

theorem tick [DecidableEq A] [DecidableEq I] (out : I) (blank marker : A) (hne : blank ≠ marker)
    (entry : Q) (m : Rule A Q I) {x y : Config A Q I} (old : advance m x = some y)
    (neg : Bool) (known : (x.tape out).pos ≠ 0 → neg = decide ((x.tape out).pos < 0)) :
    ∃ neg', ( (y.tape out).pos ≠ 0 → neg' = decide ((y.tape out).pos < 0)) ∧
      advance (rule out blank marker entry m) (running out blank marker neg x) =
        some (running out blank marker neg' y) := by
  cases h : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance,h] at old
  | some o =>
    rcases o with ⟨q',op⟩
    simp [advance,h] at old
    subst y
    let p := (x.tape out).pos
    let d := (op out).2
    obtain ⟨move,sgn⟩ := folded p neg known d
    refine ⟨_,sgn,?_⟩
    have hm := Bool.decide_congr (here blank marker hne (x.tape out).pos)
    change ((rule out blank marker entry m) (.run x.pc neg) _).map _ = _
    simp only [rule,running,banks,h,Option.map_some,Option.some.injEq,Config.mk.injEq]
    refine ⟨congrArg (fun b => Phase.run q' (foldSign b neg d)) hm,?_⟩
    funext i
    cases i with
    | some _ => rfl
    | none =>
      change (counter blank marker p.natAbs).apply
        ((counter blank marker p.natAbs).view 0,foldMove (decide ((counter blank marker p.natAbs).view 0 = marker)) neg d) =
          counter blank marker (p+d.shift).natAbs
      rw [hm]
      simp only [counter,Reset.atHead,add_zero]
      change (Reset.atHead _ _).apply _ = Reset.atHead _ _
      rw [Reset.atHead_apply,Function.update_eq_self,move]

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
