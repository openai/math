import OAI.Hierarchy.DescentPublicStepKinds
import OAI.Hierarchy.DescentCapacityCalendar
import Mathlib.Data.List.Forall2

namespace OAI
/-! # The measured reserve factor at every reset date in the public schedule -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler

private theorem append_pair {α β : Type} {r : α→β→Prop} {a a' : List α} {b b' : List β}
    (x : List.Forall₂ r a b) (y : List.Forall₂ r a' b') : List.Forall₂ r (a++a') (b++b') :=by
  induction x with
  | nil=>exact y
  | cons head tail ih=>exact .cons head ih

private theorem paired_caps (b t g height : ℕ) : List.Forall₂ (fun (tag : Bool) f=>tag=true→f=2^g)
    (kindCalendar t height) (capCalendar b t g height) :=by
  have each (n : ℕ) : ∀start,List.Forall₂ (fun (tag : Bool) f=>tag=true→f=2^g)
      (List.replicate n false) (ordinaryCapFactors b start n) :=by
    induction n with
    | zero=>intro _;exact .nil
    | succ n ih=>
      intro start
      rw [List.replicate_succ]
      exact .cons (fun h=>Bool.noConfusion h) (ih (start+1))
  have period : List.Forall₂ (fun (tag : Bool) f=>tag=true→f=2^g) (kindPeriod t) (capPeriod b t g) :=
    append_pair (each t 0) (.cons (fun _=>rfl) .nil)
  induction height with
  | zero=>exact .nil
  | succ h ih=>
    simpa only [kindCalendar,List.replicate_succ,List.flatten_cons,capCalendar] using append_pair period ih

private theorem true_at {b : ℕ} {tags : List Bool} {fs : List ℕ}
    (packed : List.Forall₂ (fun (tag : Bool) f=>tag=true→f=b) tags fs) (i : ℕ)
    (hit : (tags.drop i).head?=some true) : (fs.drop i).head?=some b :=by
  induction packed generalizing i with
  | nil=>simp at hit
  | cons head tail ih=>
    cases i with
    | zero=>simp only [List.drop_zero,List.head?_cons,Option.some.injEq] at hit ⊢;exact head hit
    | succ i=>exact ih i hit

theorem reset_cap_slot (b t g height i : ℕ) (hit : ((kindCalendar t height).drop i).head?=some true) :
    ((capCalendar b t g height).drop i).head?=some (2^g) :=
  true_at (paired_caps b t g height) i hit

theorem next_cap_product (xs : List ℕ) (i gain : ℕ) (atSlot : (xs.drop i).head?=some gain) :
    gain*((xs.take i).prod*256)=(xs.take (i+1)).prod*256 :=by
  induction i generalizing xs with
  | zero=>
    cases xs with
    | nil=>simp at atSlot
    | cons x xs=>simp only [List.drop_zero,List.head?_cons,Option.some.injEq] at atSlot; simp [atSlot]
  | succ i ih=>
    cases xs with
    | nil=>simp at atSlot
    | cons x xs=>
      have next:=ih xs atSlot
      simpa only [List.take_succ_cons,List.prod_cons,Nat.mul_left_comm,Nat.mul_assoc] using
        congrArg (x*·) next

end Hierarchy.DescentSixParty.Chronology

end OAI
