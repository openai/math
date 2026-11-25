import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationCostAddress
import OAI.Optimization.LinearProgramming.Recovery.InitialPairCost
import OAI.Optimization.LinearProgramming.Recovery.PairAccess

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open RAM RAM.Callable Polynomial

instance initialPair_fixedAccess : InitialPair.fragment.FixedAccess := by
  unfold InitialPair.fragment Odd.leaf
  infer_instance

noncomputable def pairAddresses : Polynomial ℕ :=
  addressPolynomial InitialPair.fragment InitialPair.fragmentPolynomial

/-- The physical startup bound uses only the address bank. It applies to the
actual same pair-builder ROM over any supported scalar field. -/
theorem pair_address_bound_field {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) {P : K → Prop} {front back : Memory K}
    (run : InitialPair.fragment.Run P (Odd.memory (start [] ([] : List K)).memory (start [m,d] (lpInput A b)).memory)
      (InitialPair.fragmentTime m d) (Odd.memory front back)) (j : ℕ) :
    back.index j ≤ pairAddresses.eval (m+d) :=
  logical_address_bound InitialPair.fragment InitialPair.fragmentPolynomial m d (lpInput A b)
    (InitialPair.fragmentTime_le m d) run j

theorem pair_address_bound {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    {P : ℚ → Prop} {front back : Memory ℚ}
    (run : InitialPair.fragment.Run P (Odd.memory InitialPair.blank (start [m,d] (lpInput A b)).memory)
      (InitialPair.fragmentTime m d) (Odd.memory front back)) (j : ℕ) :
    back.index j ≤ pairAddresses.eval (m+d) :=
  pair_address_bound_field A b run j

private theorem charged_capacity (cap headers worker rest : ℕ) :
    cap ≤ headers+3*(19*cap+225+(2*worker+2))+rest := by omega

private theorem capacity_le_pairTime {h n : ℕ} (l : PairBuilder.Layout h n) :
    PairBuilder.capacity h n l.previous ≤ PairBuilder.time l := by
  unfold PairBuilder.time
  exact charged_capacity _ _ _ _

/-- The initial pair builder pays for its entire numerical staging capacity in
its own clock, which already has a dimension-only polynomial bound. -/
theorem pair_capacity_le_time (m d : ℕ) :
    PairBuilder.capacity (d+1) (m+1) 0 ≤ InitialPair.fragmentTime m d :=
  (capacity_le_pairTime (InitialPair.layout m d)).trans (Nat.le_add_left ..)

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
