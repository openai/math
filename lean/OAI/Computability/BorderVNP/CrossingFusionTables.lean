import OAI.Computability.BorderVNP.CrossingFusion
import OAI.Computability.BorderVNP.CrossingFusionRate
import OAI.Computability.BorderVNP.CrossingIntegral
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The integral side tables of the fused cut

Only the occupation-state numbering is supplied as an argument. A mode-state
pair, a sequence of modes, and the padded bridge word are all numbered by
mixed-radix arithmetic. Out-of-range mode or bridge codes give zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP.Crossing

/-- Numbering of the states at each integral energy cutoff. -/
abbrev StateNumbering := ∀ E : ℕ, Fin (stateCountAt E) ≃ EnergyState E

private def extendByZero {r t : ℕ} (f : Fin r → ℤ) (k : Fin t) : ℤ :=
  if h : k.val < r then f ⟨k.val,h⟩ else 0

private theorem sum_extendByZero {r t : ℕ} (h : r ≤ t) (f g : Fin r → ℤ) :
    ∑ k : Fin t, extendByZero f k * extendByZero g k = ∑ k, f k * g k := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_trunc (hf := fun k => by simp [extendByZero, Fin.natAdd])]
  simp [extendByZero]

/-- Section 4.1 coefficient with the `2H` mode padding and explicit
numbering of the state coordinates on the two adjacent cuts. -/
noncomputable def numberedFactor {H q : ℕ} (w : WireStates H q) (num : StateNumbering)
    (E : ℕ) (reverse left : Bool) (u : Fin ((2*H)*stateCountAt (E+H)))
    (x : Fin q) (i : Fin (stateCountAt E)) : ℤ :=
  let jk := finProdFinEquiv.symm u
  extendByZero (fun j => w.factors E reverse left (j, num _ jk.2) x (num E i)) jk.1

private theorem numbered_contraction {H q : ℕ} (w : WireStates H q) (num : StateNumbering)
    (E : ℕ) (r : Bool) (x y : Fin q) (i h : Fin (stateCountAt E)) :
    (∑ u, numberedFactor w num E r true u x i * numberedFactor w num E r false u y h) =
    ∑ jk, w.factors E r true jk x (num E i) * w.factors E r false jk y (num E h) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  simp only [numberedFactor, Equiv.symm_apply_apply]
  simp_rw [sum_extendByZero w.weight_le]
  exact (num (E+H)).sum_comp (fun K => ∑ j,
    w.factors E r true (j,K) x (num E i) * w.factors E r false (j,K) y (num E h))

private noncomputable def stepAt {H q : ℕ} (w : WireStates H q) (num : StateNumbering) (E : ℕ) :
    IntegralCrossing q (stateCountAt E) ((2*H)*stateCountAt (E+H)) ((2*H)*stateCountAt (E+H)) := by
  refine ⟨numberedFactor w num _ false true, numberedFactor w num _ false false,
    numberedFactor w num _ true true, numberedFactor w num _ true false, ?_⟩
  intro x y i h
  rw [numbered_contraction, numbered_contraction, w.coefficient_identity]
  simp

private def transportStep {q s M t t' : ℕ} (h : t=t') (T : IntegralCrossing q s (M*t) (M*t)) :
    IntegralCrossing q s (M*t') (M*t') := h ▸ T

private theorem sideFactor_transport {q s M t t' : ℕ} (h : t=t') (T : IntegralCrossing q s (M*t) (M*t))
    (left b : Bool) (x : Fin q) (j : Fin M) (i : Fin s) (k : Fin t') :
    sideFactor (transportStep h T) left b x j i k = sideFactor T left b x j i (Fin.cast h.symm k) := by
  cases h
  rfl

/-- One numbered step uses the same wire-label slice at every incoming
energy. Its four arrays retain the actual coefficients from Appendix A. -/
noncomputable def numberedStep {H q : ℕ} (w : WireStates H q) (num : StateNumbering) (d : ℕ) :
    IntegralCrossing q (stateCountAt (d*H)) ((2*H)*stateCountAt ((d+1)*H))
      ((2*H)*stateCountAt ((d+1)*H)) :=
  transportStep (congrArg stateCountAt (Nat.succ_mul d H).symm) (stepAt w num (d*H))

/-- Numbered next state interpreted at the cutoff used by the operator. -/
def nextState (num : StateNumbering) (d H : ℕ) (k : Fin (stateCountAt ((d+1)*H))) :
    EnergyState (d*H+H) := num _ (Fin.cast (congrArg stateCountAt (Nat.succ_mul d H)) k)

/-- Each factor in the opened state-path expansion is exactly one of the
four signed coefficient tables, with zero at unused mode codes. -/
theorem sideFactor_numbered {H q : ℕ} (w : WireStates H q) (num : StateNumbering)
    (d : ℕ) (left b : Bool) (x : Fin q) (j : Fin (2*H))
    (i : Fin (stateCountAt (d*H))) (k : Fin (stateCountAt ((d+1)*H))) :
    sideFactor (numberedStep w num d) left b x j i k =
      if h : j.val < w.weight then w.factors (d*H) (!b) (if b then left else !left)
        (⟨j.val,h⟩, nextState num d H k) x (num _ i) else 0 := by
  rw [numberedStep, sideFactor_transport]
  cases left <;> cases b <;>
    change numberedFactor w num _ _ _ (finProdFinEquiv (j,_)) x i = _ <;>
    simp [numberedFactor, extendByZero, nextState]

private def cutNumbering (d M s : ℕ) :
    (Fin d → Fin M) × Fin s ≃ Fin (M^d*s) :=
  (finFunctionFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- The ceiling in the manuscript accommodates every mixed-radix bridge code. -/
theorem cut_capacity (m d : ℕ) (hm : 0 < m) :
    (2*leastEnergy m)^d * stateCountAt (d*leastEnergy m) ≤ (2^m)^(bridgePorts m d) := by
  let H := leastEnergy m
  have hH : (0:ℝ) < H := by exact_mod_cast (leastEnergy_spec m).1
  have hq : (0:ℝ) < stateCountAt (d*H) := by exact_mod_cast cutoffCount_pos _
  have h := Nat.le_ceil ((d * Real.logb 2 (2*(H:ℝ)) + Real.logb 2 (stateCountAt (d*H))) / m)
  have hlog : Real.logb 2 (((2*H)^d * stateCountAt (d*H) : ℕ):ℝ) ≤ (m * bridgePorts m d : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat,
      Real.logb_mul (by positivity) hq.ne', Real.logb_pow, Nat.cast_mul, mul_comm (m:ℝ)]
    exact (div_le_iff₀ (by exact_mod_cast hm)).mp h
  have hp : (0:ℝ) < (((2*H)^d * stateCountAt (d*H):ℕ):ℝ) := by push_cast; positivity
  have hc := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hp).mp hlog
  rw [Real.rpow_natCast] at hc
  rw [← pow_mul]
  exact_mod_cast hc

/-- The side tensor as a function of `d` terminal ports and `p₀` bridge ports.
The bridge word decodes to the old modes and final state, with unused words
sent to zero. -/
noncomputable def sideTable {m : ℕ} (w : WireStates (leastEnergy m) (2^m)) (num : StateNumbering)
    (left : Bool) (d : ℕ) (b : Fin d → Bool) (x : Fin d → Fin (2^m))
    (u : Fin (bridgePorts m d) → Fin (2^m)) : ℤ :=
  extendByZero (fun i =>
    let jk := (cutNumbering d (2*leastEnergy m) (stateCountAt (d*leastEnergy m))).symm i
    fusedSide (numberedStep w num) left d b x jk.1 jk.2) (finFunctionFinEquiv u)

/-- Section 4.2's antipodal tensor with the full cut padded to base-`2^m`
ports. Every one of the `2^d` summands uses the same port count. -/
theorem sideTable_identity {m : ℕ} (hm : 0 < m)
    (w : WireStates (leastEnergy m) (2^m)) (num : StateNumbering) (d : ℕ)
    (x y : Fin d → Fin (2^m)) :
    (∑ b, ∑ u, sideTable w num true d b (sideInputs b x y) u *
      sideTable w num false d b (sideInputs b y x) u) = ∏ i, if x i = y i then 1 else 0 := by
  have vacuum : stateCountAt (0 * leastEnergy m) = 1 := by
    simp [stateCountAt, cutoffCount, Lemmata.FockCircuits.partitionDimension_zero]
  rw [← fusedSides_identity vacuum (numberedStep w num)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [sideTable]
  rw [finFunctionFinEquiv.sum_comp (fun i => _ * _), sum_extendByZero (cut_capacity m d hm)]
  rw [← (cutNumbering d (2*leastEnergy m) (stateCountAt (d*leastEnergy m))).sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]

end Crossing

end BorderVNP
end Computability
end OAI
