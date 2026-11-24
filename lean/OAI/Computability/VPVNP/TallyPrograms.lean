import OAI.Computability.VPVNP.RAMTapeInputParametersMultiply
import OAI.Computability.VPVNP.RAMTapeInputParametersTriangle
import Mathlib.Data.Fintype.Sum

/-!
# Composing the fixed tally programs for the input widths

A program packages its finite control, tally update, exact instruction count and scratch
precondition. Sequential composition checks the second precondition on the first output and
counts both runs. The transition code consists of the previously verified stack routines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally

/-- A finite-control routine on unary registers together with its register update, exact
instruction count, and a proof that it realizes both on ready inputs. -/
structure Program (K : Type) [DecidableEq K] where
  /-- The finite type of local control labels of the tally routine. -/
  Q : Type
  [finite : Fintype Q]
  /-- The executable stack routine implementing the tally register update. -/
  code : Routine K Q
  /-- The final natural-number register state specified for each initial tally state. -/
  eval : State K → State K
  /-- The exact number of stack instructions used by the tally routine on a ready input. -/
  work : State K → ℕ
  /-- The precondition on the initial tally registers under which the specified update and
  instruction count hold. -/
  ready : State K → Prop
  spec : ∀ s, ready s → code.Runs (work s) (encode s) (encode (eval s))

attribute [instance] Program.finite

namespace Program

variable {K : Type} [DecidableEq K]

/-- Link the two finite controls at the normal-return boundary. -/
@[simps eval work ready]
def seq (a b : Program K) : Program K where
  Q := a.Q ⊕ b.Q
  code := a.code.followedBy b.code
  eval s := b.eval (a.eval s)
  work s := a.work s + b.work (a.eval s)
  ready s := a.ready s ∧ b.ready (a.eval s)
  spec s h := (a.spec s h.1).followedBy (b.spec _ h.2)

/-- Add a preserved source to the destination. -/
@[simps eval work ready]
def copy (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) : Program K where
  Q := _
  code := copyAdd src dst tmp
  eval s := Function.update s dst (s dst + s src)
  work s := 5 * s src + 2
  ready s := s tmp = 0
  spec s := copyAdd_runs src dst tmp hsd hst hdt s

/-- Add the product of the two preserved sources to the destination. -/
@[simps eval work ready]
def mul (lhs rhs dst outer tmp : K) (hd : [lhs, rhs, dst, outer, tmp].Nodup) : Program K where
  Q := _
  code := mulAdd lhs rhs dst outer tmp
  eval s := Function.update s dst (s dst + s lhs * s rhs)
  work s := s lhs * (5 * s rhs + 6) + 2
  ready s := s outer = 0 ∧ s tmp = 0
  spec s h := mulAdd_runs lhs rhs dst outer tmp hd s h.1 h.2

/-- Add the triangular number `1 + … + s src` to the destination. -/
@[simps eval work ready]
def triangle (src dst outer tmp : K) (hsc : src ≠ outer) (hst : src ≠ tmp)
    (hdc : dst ≠ outer) (hdt : dst ≠ tmp) (hct : outer ≠ tmp) : Program K where
  Q := _
  code := triangleAdd src dst outer tmp
  eval s := Function.update s dst (s dst + (s src + 1).choose 2)
  work s := 3 + 9 * s src + 5 * (s src).choose 2
  ready s := s outer = 0 ∧ s tmp = 0
  spec s h := triangleAdd_runs src dst outer tmp hsc hst hdc hdt hct s h.1 h.2

end Program
end RAMTape.Tally

end VPVNP
end Computability
end OAI
