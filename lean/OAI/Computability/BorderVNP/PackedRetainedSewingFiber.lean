import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.PackedInheritedObservationFiber

/-! # Complete observation fibers of the sparse zero-or-copy exterior sewing stage

The physical interval tests set absent old lanes to false and copy every live old
lane from its true sewn input. The same old independent choices occur once in
each successful observation fiber, at exactly their original addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Inherited
open scoped Classical

variable (s : Site) (loc : s.Local) {n : ℕ} (read : Fin s.incoming → Option (Fin n))
    (x : Fin n → Bool) (obs : List (Bool × Option ℕ))

/-- Original input reconstructed from the current sparse cable and free-port words. -/
def oldInput (i : Fin s.incoming) : Bool := (read i).elim false x

/-- Write the old work and its uniquely restored old incidence array. -/
def extendObservation (g : s.Fiber (oldInput s read x) obs) :
    (stage s n (intervals read)).Fiber x obs :=
  ⟨Fin.append g.val (oldInput s read x),by
    exact (stage_observe_bits s loc _ read (intervals_cover read) g.val (oldInput s read x) x).trans
      ((ite_eq_left rfl).trans g.property)⟩

/-- Invert the complete physical stage tape on the exact list of observed signs and
IDs. The absent lanes have a single legal zero filling. -/
noncomputable def stageFiberEquiv :
    s.Fiber (oldInput s read x) obs ≃ (stage s n (intervals read)).Fiber x obs :=
  Equiv.ofBijective (extendObservation s loc read x obs) <| by
    constructor
    · intro a b eq
      apply Subtype.ext
      funext i
      have h := congrArg (fun u : (stage s n (intervals read)).Fiber x obs => u.val (i.castAdd s.incoming)) eq
      exact (Fin.append_left a.val _ i).symm.trans (h.trans (Fin.append_left b.val _ i))
    · intro u
      obtain ⟨⟨g,o⟩,he⟩ := (Fin.appendEquiv (α := Bool) s.work s.incoming).surjective u.val
      change Fin.append g o = u.val at he
      have hu := (stage_observe_bits s loc (intervals read) read (intervals_cover read) g o x).symm.trans
        ((congrArg (fun w => (stage s n (intervals read)).observe (bits w x)) he).trans u.property)
      by_cases hh : o = oldInput s read x
      · subst o
        have pass : s.observe (bits g (oldInput s read x)) = some obs :=
          (ite_eq_left (show oldInput s read x = (fun k => (read k).elim false x) from rfl)).symm.trans hu
        exact ⟨⟨g,pass⟩,Subtype.ext he⟩
      · have hn : o ≠ fun k => (read k).elim false x := hh
        have bad : (none : Option (List (Bool × Option ℕ))) = some obs := (ite_eq_right hn).symm.trans hu
        contradiction

/-- The fiber map acts on actual private bits by appending the restored incidence array. -/
theorem stageFiberEquiv_val (g : s.Fiber (oldInput s read x) obs) :
    (stageFiberEquiv s loc read x obs g).val = Fin.append g.val (oldInput s read x) := rfl

end Packing.SewnField

end BorderVNP
end Computability
end OAI
