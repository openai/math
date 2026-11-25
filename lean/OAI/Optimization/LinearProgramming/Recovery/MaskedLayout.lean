import OAI.Optimization.LinearProgramming.Recovery.PairBuilderLayout

/-! Addresses of the input, support flags, augmented equations and worker tables. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedInput

def words (h n : ℕ) := h*n+n
def base (h n : ℕ) := 256+words h n
def bottom (h n : ℕ) := base h n+h*n
def flagBase (h n : ℕ) := bottom h n+n*n
def outputBase (h n : ℕ) := flagBase h n+n
def scratchBase (h n : ℕ) := outputBase h n+n*n

def pairLayout (h n : ℕ) : PairBuilder.Layout (h+n) n where
  src:=base h n
  out:=outputBase h n
  scratch:=scratchBase h n
  previous:=0
  minimum:=by unfold base;omega
  sourceRoom:=by unfold outputBase flagBase bottom;rw [Nat.add_mul];omega
  outputRoom:=le_rfl

end MaskedInput
end Recovery
end LinearProgramming
end Optimization
end OAI
