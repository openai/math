import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.SimpRw

/-! Integral allocations for the balanced-price network in Section 4. Each row is an
expert's flow on its incident arcs. The `none` column is its outside-option arc. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Optimum

open scoped BigOperators

variable {E G : Type*} [Fintype E] [Fintype G]

/-- Multiplying a column by the expert signs yields its outgoing-minus-incoming balance. -/
def sign (positive : E → Bool) (e : E) : ℚ := if positive e then 1 else -1

/-- The outside option has a zero-weight arc. -/
def arcWeight (c : E → G → ℚ) (e : E) : Option G → ℚ
  | none => 0
  | some i => c e i

/-- Conservation at experts and real goods, with zero flow on unavailable arcs. -/
structure Feasible (positive : E → Bool) (units : E → ℕ) (accepts : E → G → Prop)
    (f : E → Option G → ℕ) : Prop where
  row : ∀ e, ∑ o, f e o = units e
  unavailable : ∀ e i, ¬ accepts e i → f e (some i) = 0
  good : ∀ i, ∑ e, sign positive e * (f e (some i) : ℚ) = 0

/-- The total weight of the integral flow. -/
def value (c : E → G → ℚ) (f : E → Option G → ℕ) : ℚ :=
  ∑ e, ∑ o, arcWeight c e o * (f e o : ℚ)

/-- Send each entire expert row to its outside-option arc. -/
def dummyFlow (units : E → ℕ) (e : E) : Option G → ℕ
  | none => units e
  | some _ => 0

theorem feasible_dummyFlow (positive : E → Bool) (units : E → ℕ) (accepts : E → G → Prop) :
    Feasible positive units accepts (dummyFlow units) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    simp [Fintype.sum_option, dummyFlow]
  · intro e i _
    rfl
  · intro i
    simp [dummyFlow]

theorem Feasible.entry_le {positive : E → Bool} {units : E → ℕ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} (hf : Feasible positive units accepts f) (e : E) (o : Option G) :
    f e o ≤ units e := by
  rw [← hf.row e]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (f e i)) (Finset.mem_univ o)

/-- A finite maximum exists, including with empty index sets or zero supplies. -/
theorem exists_maximum (positive : E → Bool) (units : E → ℕ) (accepts : E → G → Prop)
    (c : E → G → ℚ) : ∃ f : E → Option G → ℕ, Feasible positive units accepts f ∧
      ∀ f', Feasible positive units accepts f' → value c f' ≤ value c f := by
  classical
  let B := (e : E) → Option G → Fin (units e + 1)
  let _ : Fintype B := inferInstanceAs (Fintype ((e : E) → Option G → Fin (units e + 1)))
  let decode (a : B) (e : E) (o : Option G) : ℕ := (a e o).val
  let encode (f : E → Option G → ℕ) (hf : Feasible positive units accepts f) : B :=
    fun e o => ⟨f e o, Nat.lt_succ_of_le (hf.entry_le e o)⟩
  let options : Finset B := Finset.univ.filter fun a => Feasible positive units accepts (decode a)
  have mem_encode (f : E → Option G → ℕ) (hf : Feasible positive units accepts f) :
      encode f hf ∈ options := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  obtain ⟨a, ha, hmax⟩ := options.exists_max_image (fun a => value c (decode a))
    ⟨_, mem_encode _ (feasible_dummyFlow positive units accepts)⟩
  have ha' : Feasible positive units accepts (decode a) :=
    (Finset.mem_filter.mp (show a ∈ Finset.univ.filter (fun b : B => Feasible positive units accepts (decode b)) from ha)).2
  refine ⟨decode a, ha', ?_⟩
  intro f hf
  exact hmax (encode f hf) (mem_encode f hf)

/-- An integral residual change obeys reverse capacities and preserves all balances. -/
structure Circulation (positive : E → Bool) (accepts : E → G → Prop)
    (f : E → Option G → ℕ) (z : E → Option G → ℤ) : Prop where
  capacity : ∀ e o, 0 ≤ (f e o : ℤ) + z e o
  unavailable : ∀ e i, ¬ accepts e i → z e (some i) = 0
  row : ∀ e, ∑ o, z e o = 0
  good : ∀ i, ∑ e, sign positive e * (z e (some i) : ℚ) = 0

/-- Push an integral change through the residual network. -/
def perturb (f : E → Option G → ℕ) (z : E → Option G → ℤ) (e : E) (o : Option G) : ℕ :=
  ((f e o : ℤ) + z e o).toNat

theorem Circulation.cast_perturb {positive : E → Bool} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} {z : E → Option G → ℤ} (hz : Circulation positive accepts f z)
    (e : E) (o : Option G) : (perturb f z e o : ℤ) = (f e o : ℤ) + z e o :=
  Int.toNat_of_nonneg (hz.capacity e o)

theorem Circulation.ratCast_perturb {positive : E → Bool} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} {z : E → Option G → ℤ} (hz : Circulation positive accepts f z)
    (e : E) (o : Option G) : (perturb f z e o : ℚ) = (f e o : ℚ) + (z e o : ℚ) := by
  exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) (hz.cast_perturb e o)

theorem Circulation.feasible_perturb {positive : E → Bool} {units : E → ℕ}
    {accepts : E → G → Prop} {f : E → Option G → ℕ} {z : E → Option G → ℤ}
    (hz : Circulation positive accepts f z) (hf : Feasible positive units accepts f) :
    Feasible positive units accepts (perturb f z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have heq : ∑ o, (perturb f z e o : ℤ) = (units e : ℤ) := by
      simp_rw [hz.cast_perturb]
      rw [Finset.sum_add_distrib, hz.row e, add_zero]
      exact_mod_cast hf.row e
    exact_mod_cast heq
  · intro e i hi
    simp [perturb, hf.unavailable e i hi, hz.unavailable e i hi]
  · intro i
    simp_rw [hz.ratCast_perturb, mul_add]
    rw [Finset.sum_add_distrib, hf.good i, hz.good i, add_zero]

theorem Circulation.value_perturb {positive : E → Bool} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} {z : E → Option G → ℤ} (hz : Circulation positive accepts f z)
    (c : E → G → ℚ) :
    value c (perturb f z) = value c f + ∑ e, ∑ o, arcWeight c e o * (z e o : ℚ) := by
  simp only [value, hz.ratCast_perturb, mul_add, Finset.sum_add_distrib]

/-- An optimum admits no positive-weight capacity-respecting residual circulation. -/
theorem residual_nonpositive {positive : E → Bool} {units : E → ℕ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} (hf : Feasible positive units accepts f) (c : E → G → ℚ)
    (hmax : ∀ f', Feasible positive units accepts f' → value c f' ≤ value c f)
    {z : E → Option G → ℤ} (hz : Circulation positive accepts f z) :
    ∑ e, ∑ o, arcWeight c e o * (z e o : ℚ) ≤ 0 := by
  have h := hmax _ (hz.feasible_perturb hf)
  rwa [hz.value_perturb, add_le_iff_nonpos_right] at h

/-- The difference of two feasible market flows is an integral residual circulation. -/
theorem Feasible.circulation_sub {positive : E → Bool} {units : E → ℕ}
    {accepts : E → G → Prop} {f f' : E → Option G → ℕ}
    (hf' : Feasible positive units accepts f') (hf : Feasible positive units accepts f) :
    Circulation positive accepts f (fun e o => (f' e o : ℤ) - f e o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e o
    omega
  · intro e i hi
    rw [hf'.unavailable e i hi, hf.unavailable e i hi, sub_self]
  · intro e
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (by exact_mod_cast (hf'.row e).trans (hf.row e).symm)
  · intro i
    simp_rw [Int.cast_sub, Int.cast_natCast, mul_sub]
    rw [Finset.sum_sub_distrib, hf'.good, hf.good, sub_self]

/-- Integral optimality is equivalent to the residual variational inequality. -/
theorem optimal_iff_residual {positive : E → Bool} {units : E → ℕ} {accepts : E → G → Prop}
    {f : E → Option G → ℕ} (hf : Feasible positive units accepts f) (c : E → G → ℚ) :
    (∀ f', Feasible positive units accepts f' → value c f' ≤ value c f) ↔
      ∀ z, Circulation positive accepts f z →
        ∑ e, ∑ o, arcWeight c e o * (z e o : ℚ) ≤ 0 := by
  refine ⟨fun hmax _ hz => residual_nonpositive hf c hmax hz, ?_⟩
  intro h f' hf'
  have hz := hf'.circulation_sub hf
  have hgain := h _ hz
  simp_rw [Int.cast_sub, Int.cast_natCast, mul_sub] at hgain
  simpa only [value, Finset.sum_sub_distrib, sub_nonpos] using hgain

end Optimum
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
