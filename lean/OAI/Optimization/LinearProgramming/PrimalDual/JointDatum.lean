import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

variable {K : Type*}

/-- A word of the joint instance either is a small constant or copies one signed input word. -/
inductive JointDatum where
  | zero
  | negOne
  | source (idx : Nat) (negate : Bool)
  deriving DecidableEq, Repr

def JointDatum.read [Ring K] (src : Nat → K) : JointDatum → K
  | .zero => 0
  | .negOne => -1
  | .source k false => src k
  | .source k true => -src k

/-- The canonical coefficient at row `r`, column `j`. With `j = d+m` this
returns that row's right-hand side, which the RAM writes after the matrix. -/
def jointDatum (m d r j : Nat) : JointDatum :=
  if j < d + m then
    if r < m then
      if j < d then .source (r * d + j) false else .zero
    else if r < m + m then
      if j = d + (r - m) then .negOne else .zero
    else if r < m + m + d then
      if j < d then .zero else .source ((j - d) * d + (r - (m + m))) false
    else if r < m + m + d + d then
      if j < d then .zero else .source ((j - d) * d + (r - (m + m + d))) true
    else
      if j < d then .source (m * d + m + j) true else .source (m * d + (j - d)) false
  else
    if r < m then .source (m * d + r) false
    else if r < m + m then .zero
    else if r < m + m + d then .source (m * d + m + (r - (m + m))) false
    else if r < m + m + d + d then .source (m * d + m + (r - (m + m + d))) true
    else .zero

end PrimalDual
end LinearProgramming
end Optimization
end OAI
