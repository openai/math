import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationCostPair
import OAI.Optimization.LinearProgramming.Recovery.GlobalCapacity
import OAI.Optimization.LinearProgramming.NormalSubspace.Calls

/-! The fixed finite initial orientation program, its dimension-only clock, and
bounds on every logical caller address after the initial and completed prefixes. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open RAM RAM.Callable Polynomial

noncomputable def program (solver : NormalSubspace.Spec) : Fragment :=
  InitialPair.fragment.seq ((NormalSubspace.call solver 154).seq
    (Odd.leaf (SupportBundle.select (Principal.capacityC solver) (Principal.capacityE solver))))

instance program_fixedAccess (solver : NormalSubspace.Spec) : (program solver).FixedAccess := by
  unfold program NormalSubspace.call Fragment.stage Odd.leaf
  infer_instance

noncomputable def clock (solver : NormalSubspace.Spec) : Polynomial ℕ :=
  InitialPair.fragmentPolynomial +
    ((19*InitialPair.fragmentPolynomial+225+(2*solver.clock.comp (X+1)+2)) +
     4*(SupportBundle.selectTime (Principal.capacityC solver) (Principal.capacityE solver)).comp (pairAddresses+1))

theorem clock_eval (solver : NormalSubspace.Spec) (u : ℕ) :
    (clock solver).eval u = InitialPair.fragmentPolynomial.eval u +
      ((19*InitialPair.fragmentPolynomial.eval u+225+(2*solver.clock.eval (u+1)+2)) +
       4*(SupportBundle.selectTime (Principal.capacityC solver) (Principal.capacityE solver)).eval
         (pairAddresses.eval u+1)) := by simp [clock]

theorem clock_bound (solver : NormalSubspace.Spec) (m d : ℕ) :
    InitialPair.fragmentTime m d +
      (NormalSubspace.callTime solver (PairBuilder.capacity (d+1) (m+1) 0) (m+1) +
       4*(SupportBundle.selectTime (Principal.capacityC solver) (Principal.capacityE solver)).eval
         (pairAddresses.eval (m+d)+1)) ≤ (clock solver).eval (m+d) := by
  have pair := InitialPair.fragmentTime_le m d
  have capacity := (pair_capacity_le_time m d).trans pair
  have dimension : m+1 ≤ m+d+1 := by omega
  have subspace := InitialPair.eval_le solver.clock dimension
  have call : NormalSubspace.callTime solver (PairBuilder.capacity (d+1) (m+1) 0) (m+1) ≤
      19*InitialPair.fragmentPolynomial.eval (m+d)+225+(2*solver.clock.eval (m+d+1)+2) := by
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 19 capacity) 225)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 subspace) 2)
  rw [clock_eval]
  exact Nat.add_le_add pair (Nat.add_le_add_right call _)

noncomputable def finalAddresses (solver : NormalSubspace.Spec) : Polynomial ℕ :=
  addressPolynomial (program solver) (clock solver)

/-- The caller's final address bound is uniform across scalar fields executing
the same finite program and clock. -/
theorem final_address_bound_field (solver : NormalSubspace.Spec)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) {P : K → Prop} {front back : Memory K}
    (run : (program solver).Run P (Odd.memory (start [] ([] : List K)).memory (start [m,d] (lpInput A b)).memory)
      ((clock solver).eval (m+d)) (Odd.memory front back)) (j : ℕ) :
    back.index j ≤ (finalAddresses solver).eval (m+d) :=
  logical_address_bound (program solver) (clock solver) m d (lpInput A b) le_rfl run j

theorem final_address_bound (solver : NormalSubspace.Spec) {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {P : ℚ → Prop} {front back : Memory ℚ}
    (run : (program solver).Run P (Odd.memory InitialPair.blank (start [m,d] (lpInput A b)).memory)
      ((clock solver).eval (m+d)) (Odd.memory front back)) (j : ℕ) :
    back.index j ≤ (finalAddresses solver).eval (m+d) :=
  final_address_bound_field solver A b run j

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
