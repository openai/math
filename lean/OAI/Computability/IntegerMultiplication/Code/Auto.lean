import OAI.Computability.IntegerMultiplication.Code.List
import OAI.Computability.IntegerMultiplication.Code.Finite
import Mathlib.Tactic.FunProp

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
attribute [fun_prop] Easy
attribute [fun_prop] Easy.compose Easy.const Easy.pair Easy.fstCompose Easy.sndCompose Easy.cons
  Easy.leftSum Easy.rightSum

variable {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z]
@[fun_prop] theorem easy_id : Easy (fun x : X => x) := Easy.identity

@[fun_prop] theorem easy_reverse {g : X → List Y} (h : Easy g) :
    Easy (fun x => (g x).reverse) := h.compose Easy.reverse

@[fun_prop] theorem easy_append {f g : X → List Y} (h : Easy f) (e : Easy g) :
    Easy (fun x => f x ++ g x) := (h.pair e).compose Easy.append

@[fun_prop] theorem easy_flatten {f : X → List (List Y)} (h : Easy f) :
    Easy (fun x => (f x).flatten) := h.compose Easy.flatten

@[fun_prop] theorem easy_map {f : X → List Y} {g : Y → Z} (h : Easy f) (e : Easy g) :
    Easy (fun x => (f x).map g) := h.compose e.mapping

theorem Easy.some : Easy (fun x : X => some x) :=
  (Task.tag true send).mono (by simp)

@[fun_prop] theorem easy_some {f : X → Y} (h : Easy f) :
    Easy (fun x => some (f x)) := h.compose Easy.some

end Code

end IntegerMultiplication
end Computability
end OAI
