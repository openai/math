import OAI.Optimization.LinearProgramming.Compression.AddressCapacity
import OAI.Optimization.LinearProgramming.Compression.BitBudget
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests
import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Dimension-only register extents and clocks shared by the rational and real
implementations of the minor service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceBudget
open RAM GeneratorTable

def live (n g : ℕ) := slotBase n (g+2)+g+1

theorem live_le (n g : ℕ) (hg : g ≤ paperWidth n) : live n g ≤ 30*(n+1)^8 := by
  change g ≤ (n+1)^6 at hg
  calc
    live n g ≤ 7+n*n+((n+1)^6+2)*(2*n+3)+(n+1)^6+1 := by
      unfold live slotBase tableBase stride
      gcongr
    _ ≤ 30*(n+1)^8 := by ring_nf; omega

theorem dimensions_le_live (n g : ℕ) : n ≤ live n g ∧ g ≤ live n g ∧ 7 ≤ live n g := by
  have hn := Nat.le_mul_self n
  unfold live slotBase tableBase
  omega

noncomputable def coefficient (time : Polynomial ℕ) := 2*time.eval 1+4*onlineMinorBitPolynomial.eval 1+400

noncomputable def exponent (time : Polynomial ℕ) := max 8 (max time.natDegree onlineMinorBitPolynomial.natDegree)

/-- This is exactly the output of the address-only `monomialCapacity` initializer used
by the enclosing numerical call. `rom` is the static maximum physical address of its code. -/
noncomputable def capacity (time : Polynomial ℕ) (rom n : ℕ) :=
  coefficient time*(n+1)^exponent time+(rom+114)

theorem capacity_bounds (time : Polynomial ℕ) (rom n g : ℕ) (hg : g ≤ paperWidth n) :
    let B := capacity time rom n
    let U := max (2*live n g+114) (2*n+114)
    114 ≤ B ∧ max rom U+(2*time.eval n+2) ≤ B ∧
      2*(3+2*onlineMinorBitPolynomial.eval n+2) ≤ B := by
  let E := exponent time
  let X := (n+1)^E
  have ev (j : ℕ) (hj : j ≤ E) : (n+1)^j ≤ X := Nat.pow_le_pow_right (Nat.succ_pos _) hj
  have ts : time.eval n ≤ time.eval 1*X := (polynomial_eval_le_polyBound time n).trans
    (Nat.mul_le_mul_left _ (ev time.natDegree (by dsimp [E,exponent]; omega)))
  have ps : onlineMinorBitPolynomial.eval n ≤ onlineMinorBitPolynomial.eval 1*X :=
    (polynomial_eval_le_polyBound onlineMinorBitPolynomial n).trans
      (Nat.mul_le_mul_left _ (ev _ (by dsimp [E,exponent]; omega)))
  have ls : live n g ≤ 30*X := (live_le n g hg).trans
    (Nat.mul_le_mul_left _ (ev 8 (by dsimp [E,exponent]; omega)))
  have leN := (dimensions_le_live n g).1
  have xpos : 1 ≤ X := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have eq : capacity time rom n=2*(time.eval 1*X)+4*(onlineMinorBitPolynomial.eval 1*X)+400*X+rom+114 := by
    unfold capacity coefficient
    change (2*time.eval 1+4*onlineMinorBitPolynomial.eval 1+400)*X+(rom+114)=_
    ring
  dsimp only
  rw [eq]
  omega

end ServiceBudget
end Compression
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServicePrepare

open ServiceBudget

/-- The fixed address-capacity setup and the finite save, clear and fill stages. -/
noncomputable def work (time : Polynomial ℕ) (rom n g : ℕ) :=
  (monomialCapacityTime (coefficient time) (exponent time)).eval n+
    (12*live n g+28+(10*capacity time rom n+150+40*(n+live n g+1)))

end ServicePrepare
end Compression
end LinearProgramming
end Optimization
end OAI
