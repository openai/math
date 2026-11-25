import OAI.Computability.NearSquareRoot.CommonAlphabetLayout
import Mathlib.Tactic.DeriveFintype

/-! # Explicit physical controller for fixed-width alphabet blocks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type}

inductive Mode | write | align₁ | align₂

private def modeTag : Mode → Fin 3
  | .write => 0 | .align₁ => 1 | .align₂ => 2

private instance : Finite Mode := Finite.of_injective modeTag (by
  intro a b h; cases a <;> cases b <;> first | rfl | exact False.elim ((of_decide_eq_false rfl) h))

abbrev Letters (w : ℕ) := Fin w → Option Bool

/-- The controller keeps just the finite source control state, the last tuple of read
symbols or actions, one in-block position and a finite read buffer. -/
inductive PC (A Q I : Type) (w : ℕ)
  | ready (q : Q) (a : I → A)
  | work (q : Q) (op : I → A × TM.Move) (mode : Mode) (j : Fin w)
  | readBlock (q : Q) (buf : I → Letters w) (j : Fin w)
  | rewind (q : Q) (a : I → A) (j : Fin w)

private def moveTag : TM.Move → Fin 3
  | .left => 0 | .stay => 1 | .right => 2

private instance : Finite TM.Move := Finite.of_injective moveTag (by
  intro a b h; cases a <;> cases b <;> first | rfl | exact False.elim ((of_decide_eq_false rfl) h))

instance {w : ℕ} [Finite A] [Finite Q] [Finite I] : Finite (PC A Q I w) := by
  let tags : PC A Q I w → (Q × (I → A)) ⊕
      (Q × (I → A × TM.Move) × Mode × Fin w) ⊕
      (Q × (I → Letters w) × Fin w) ⊕ (Q × (I → A) × Fin w) := fun
    | .ready q a => .inl (q,a)
    | .work q op m j => .inr (.inl (q,op,m,j))
    | .readBlock q buf j => .inr (.inr (.inl (q,buf,j)))
    | .rewind q a j => .inr (.inr (.inr (q,a,j)))
  apply Finite.of_injective tags
  rintro (_ | _ | _ | _) (_ | _ | _ | _) h <;> simp_all [tags]

variable (c : Code A)
def first : Fin c.width := ⟨0, c.pos⟩
def emptyBuffer : I → Letters c.width := fun _ _ => none

/-- Either advance to the next cell index or switch phases at the end of the block. -/
def atIndex {R : Type*} (w : ℕ) (inside : Fin w → R) (done : R) (j : ℕ) : R :=
  if hj : j < w then inside ⟨j, hj⟩ else done

def turn₁ : TM.Move → TM.Move | .right => .stay | _ => .left
def turn₂ : TM.Move → TM.Move | .left => .left | _ => .stay

theorem aligned (a : TM.Move) :
    1 + (turn₁ a).shift + (turn₂ a).shift = a.shift := by cases a <;> rfl

def hold (a : I → Option Bool) (moves : I → TM.Move) := fun i => (a i, moves i)

def stash {w : ℕ} (buf : I → Letters w) (j : Fin w) (a : I → Option Bool) : I → Letters w :=
  fun i => Function.update (buf i) j (a i)

def readStart (q : Q) : PC A Q I c.width := .readBlock q (emptyBuffer c) (first c)

def rule (m : TM.Rule A Q I) : TM.Rule (Option Bool) (PC A Q I c.width) I
  | .ready q cached, a =>
    (m q cached).map fun (q',op) => (.work q' op .write (first c), hold a (fun _ => .stay))
  | .work q op .write j, _ =>
    some (atIndex _ (.work q op .write) (.work q op .align₁ (first c)) (j.val+1),
      fun i => (c.enc (op i).1 j, .right))
  | .work q op .align₁ j, a =>
    some (atIndex _ (.work q op .align₁) (.work q op .align₂ (first c)) (j.val+1),
      hold a (fun i => turn₁ (op i).2))
  | .work q op .align₂ j, a =>
    some (atIndex _ (.work q op .align₂) (readStart c q) (j.val+1),
      hold a (fun i => turn₂ (op i).2))
  | .readBlock q buf j, a =>
    let buf' := stash buf j a
    some (atIndex _ (.readBlock q buf') (.rewind q (fun i => c.dec (buf' i)) (first c)) (j.val+1),
      hold a (fun _ => .right))
  | .rewind q cached j, a =>
    some (atIndex _ (.rewind q cached) (.ready q cached) (j.val+1), hold a (fun _ => .left))

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
