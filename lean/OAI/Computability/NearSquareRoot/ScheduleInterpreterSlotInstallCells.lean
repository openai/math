import OAI.Computability.NearSquareRoot.ScheduleInterpreterInit

/-! # Absolute cell contents during installation of the shared raw tape fences -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotInstall
open IntegerMultiplication TM
variable {A I Q : Type}

def base (q : Q) (contents : I → ℤ → A) : Config A Q I :=
  ⟨q, fun j => ⟨0,contents j⟩⟩

def paint (contents : I → ℤ → A) (L : ℕ) (origin right : Bool) (left : I → Bool)
    (j : I) (p : ℤ) : Fence.Symbol A :=
  (contents j p, (origin && decide (p=0)) || (left j && decide (p = -(L:ℤ))),
    (origin && decide (p=0)) || (right && decide (p = (L:ℤ))))

def atOrigin (c : Fence.Symbol A) := c.2.1 && c.2.2

def rightEnd (c : Fence.Symbol A) := !c.2.1 && c.2.2

def stamp (b : Bool) (c : Fence.Symbol A) : Fence.Symbol A := (c.1,b,b)

def writeRight (c : Fence.Symbol A) : Fence.Symbol A := (c.1,c.2.1,true)

def writeLeft [DecidableEq I] (g j : I) (c : Fence.Symbol A) : Fence.Symbol A :=
  if j = g then c else (c.1,true,c.2.2)

def originRule (b : Bool) : Rule (Fence.Symbol A) Bool I
  | false,h => some (true, fun j => (stamp b (h j),.stay))
  | true,_ => none

theorem origin_run (f : I → ℤ → A) (L : ℕ) (hL : 0 < L) (b a right : Bool) (left : I → Bool) :
    Trace (advance (originRule b)) (base false (paint f L a right left)) 1
      (base true (paint f L b right left)) := by
  apply Trace.single
  simp only [advance,originRule,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and,
    base,Tape.apply,Move.shift,Int.add_zero]
  funext j
  apply congrArg (Tape.mk 0)
  funext p
  by_cases h : p=0
  · subst p
    simp [stamp,paint,show (0 : ℤ) ≠ -(L : ℤ) by omega,show (0 : ℤ) ≠ L by omega]
  · simp [paint,h]

theorem origin_halt (b : Bool) (f : I → ℤ → Fence.Symbol A) :
    advance (originRule b) (base true f) = none := rfl

def loaded [DecidableEq I] (inp : I) (blank : A) (s : List A) (j : I) : Tape A :=
  Tape.loaded blank (if j=inp then s else [])

def plain [DecidableEq I] (inp : I) (blank : A) (s : List A) (j : I) : Tape (Fence.Symbol A) :=
  Tape.loaded (FenceInit.plain blank) ((if j=inp then s else []).map FenceInit.plain)

theorem plain_eq [DecidableEq I] (inp : I) (blank : A) (s : List A) (q : Q) :
    (⟨q,plain inp blank s⟩ : Config (Fence.Symbol A) Q I) =
      base q (paint (fun j => (loaded inp blank s j).view) s.length false false (fun _ => false)) := by
  apply congrArg (Config.mk q)
  funext j
  apply congrArg (Tape.mk 0)
  funext p
  cases p with
  | negSucc => rfl
  | ofNat k =>
    simp [paint,loaded,Tape.loaded,List.getElem?_map,FenceInit.plain]
    cases (if j=inp then s else [])[k]? <;> rfl

theorem marked_eq [DecidableEq I] (inp : I) (blank : A) (s : List A) (q : Q) :
    base q (paint (fun j => (loaded inp blank s j).view) s.length false true (fun _ => true)) =
      ⟨q,fun j => Fence.markedTape (-(s.length : ℤ)) s.length (loaded inp blank s j)⟩ := by
  apply congrArg (Config.mk q)
  funext j
  apply congrArg (Tape.mk 0)
  funext p
  simp [paint,loaded,Tape.loaded,Fence.bits]

theorem read_nonblank [DecidableEq I] (inp : I) (blank : A) (s : List A) (hn : blank ∉ s)
    {k : ℕ} (hk : k<s.length) : (loaded inp blank s inp).view k ≠ blank := by
  simp only [loaded,ite_true,Tape.loaded,List.getElem?_eq_getElem hk,Option.getD_some]
  intro h
  exact hn (h ▸ List.getElem_mem hk)

theorem read_end [DecidableEq I] (inp : I) (blank : A) (s : List A) :
    (loaded inp blank s inp).view s.length = blank := by simp [loaded,Tape.loaded]

end Uniform.SlotInstall

end NearSquareRoot
end Computability
end OAI
