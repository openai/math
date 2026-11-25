import OAI.Hierarchy.DescentRestrictedCalendarDegree
import OAI.Hierarchy.DescentGroupStageData

namespace OAI
/-! # Paying the public degree for the reachable addresses of a grouped stage -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentHostDirectory DescentHostDegree
open scoped BigOperators Classical
noncomputable section

variable {P F J V : Type} {d k slots n : ℕ} {bits : P → ℕ}
  [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price reserve : ℝ}

/-- Keep the entire physical stage and certify its record and root bills at the
calendar degree using the distinct addresses of its actual ten-hop directory. -/
def withCalendarDegree (stage : GroupStage W G price reserve J (Host V k slots) n)
    (near : V → Finset V) (D Δ : ℕ) (old : ∀ v, (near v).card ≤ Δ)
    (directory : stage.near = restrictedNear near D k slots) (enough : 3 ≤ slots)
    (budget : ℝ)
    (records : price * stage.hist * ((∑ u, (stage.records u).length : ℕ) : ℝ) ≤ budget)
    (roots : ((Fintype.card J * (Fintype.card V * 2^(k+1) * slots) : ℕ) : ℝ) *
      ((2 : ℝ)^packExponent 20 (((Δ+1)*(D+1+2^D)*slots)^10) *
        (price * ((stage.wire * (stage.z*G.b) * stage.cap : ℕ) : ℝ))) ≤ budget) :
    GroupStage W G price budget J (Host V k slots) n := by
  let branch := (Δ+1)*(D+1+2^D)*slots
  have base : 2 ≤ branch := (by omega : 2 ≤ slots).trans
    (Nat.le_mul_of_pos_left slots (by positivity : 0 < (Δ+1)*(D+1+2^D)))
  refine { stage with
    degree := branch^10
    degreeMin := (by decide : 2 ≤ 2^10).trans (Nat.pow_le_pow_left base 10)
    degreeBound := ?_
    retained := ?_
    roots := ?_ }
  · rw [directory]
    exact restricted_degree_calendar near D k slots Δ old enough
  · simpa only [Nat.cast_sum] using records
  · have counted := Nat.mul_le_mul_left (Fintype.card J) (host_size (V:=V) (k:=k) (slots:=slots))
    have nonneg : 0 ≤ (2 : ℝ)^packExponent 20 (branch^10) *
        (price * ((stage.wire * (stage.z*G.b) * stage.cap : ℕ) : ℝ)) :=
      mul_nonneg (by positivity) (mul_nonneg stage.pricePos.le (by positivity))
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr counted) nonneg).trans roots

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
