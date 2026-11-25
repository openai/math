import OAI.Optimization.LinearProgramming.Compression.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! ## A finite rational matrix for the simultaneous clipping constraints

A signed logarithmic comparison uses at most four terms including multiplicities.
Keeping that sparsity when coefficients are added bounds denominators independently of
the total number of minor indices.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The signed four-term comparisons, including repeated and cancelling terms. -/
abbrev BoundedForm (ι : Type*) [Fintype ι] := {a : ι → ℤ // ∑ i, (a i).natAbs ≤ 4}

private theorem coord_natAbs_le (a : BoundedForm ι) (i : ι) : (a.val i).natAbs ≤ 4 :=
  (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (a.val j).natAbs)
    (Finset.mem_univ i)).trans a.property

noncomputable instance : Fintype (BoundedForm ι) := by
  classical
  let encode : BoundedForm ι → ι → Set.Icc (-4 : ℤ) 4 := fun a i =>
    ⟨a.val i, by
      have h := coord_natAbs_le a i
      have hh : |a.val i| ≤ (4:ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h
      exact abs_le.mp hh⟩
  exact Fintype.ofInjective encode fun a b h => Subtype.ext (funext fun i =>
    congrArg Subtype.val (congrFun h i))

/-- Combine the rational coefficients of a single coordinate, or the offsets, before
applying the row to a generator vector. -/
def boundedSum (a : BoundedForm ι) (v : ι → ℚ) : ℚ := ∑ i, (a.val i : ℚ) * v i

/-- Expanding the affine family commutes with applying the signed integer comparison. -/
theorem intForm_eval_eq (a : BoundedForm ι) (F : AffineFamily ι κ) (y : κ → ℝ) :
    intForm a.val (F.eval y) =
      (∑ j, (boundedSum a (fun i => F.coefficient i j) : ℝ) * y j) + boundedSum a F.offset := by
  simp only [intForm, AffineFamily.eval, boundedSum, mul_add, Finset.sum_add_distrib,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- Each clipping condition is presented by two upper bounds. A one-sided condition
uses the same halfspace twice. The factor of the value is always `1` or `-1`. -/
def ClipRow.halfspace (r : ClipRow) (upper : Bool) : ℚ × ℚ :=
  match r with
  | .lower lo => (-1, -lo)
  | .upper hi => (1, hi)
  | .interval lo hi => if upper then (1, hi) else (-1, -lo)

theorem ClipRow.holds_iff_halfspaces (r : ClipRow) (v : ℝ) :
    r.Holds v ↔ ∀ s, ((r.halfspace s).1 : ℝ) * v ≤ (r.halfspace s).2 := by
  cases r <;> simp [ClipRow.Holds, ClipRow.halfspace, Bool.forall_bool]

theorem ClipRow.halfspace_sign (r : ClipRow) (s : Bool) :
    (r.halfspace s).1 = 1 ∨ (r.halfspace s).1 = -1 := by
  cases r <;> cases s <;> simp [ClipRow.halfspace]

/-- The signed coefficients of each clipping inequality in standard `A y ≤ b` form. -/
noncomputable def clippingMatrix (F : AffineFamily ι κ) (B η : ℚ) (trueLog : ι → ℝ) :
    Matrix (BoundedForm ι × Bool) κ ℚ := fun (a,s) j =>
  ((comparisonRow B η (intForm a.val trueLog)).halfspace s).1 *
    boundedSum a (fun i => F.coefficient i j)

noncomputable def clippingRhs (F : AffineFamily ι κ) (B η : ℚ) (trueLog : ι → ℝ) :
    (BoundedForm ι × Bool) → ℚ := fun (a,s) =>
  let h := (comparisonRow B η (intForm a.val trueLog)).halfspace s
  h.2 - h.1 * boundedSum a F.offset

private theorem abs_sum_cast {a : ι → ℤ} :
    (∑ i, |(a i : ℝ)|) = ((∑ i, (a i).natAbs : ℕ) : ℝ) := by
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs]

/-- A real generator vector obeys all the true comparison rows exactly when it satisfies
the finite rational matrix system. -/
theorem comparisonRows_iff_mulVec_le (F : AffineFamily ι κ) (B η : ℚ)
    (trueLog : ι → ℝ) (y : κ → ℝ) :
    (∀ a : ι → ℤ, (∑ i, |(a i : ℝ)|) ≤ 4 →
      (comparisonRow B η (intForm a trueLog)).Holds (intForm a (F.eval y))) ↔
    (clippingMatrix F B η trueLog).map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
      (fun t => (clippingRhs F B η trueLog t : ℝ)) := by
  have row (a : BoundedForm ι) (s : Bool) :
      (let h := (comparisonRow B η (intForm a.val trueLog)).halfspace s
       (h.1 : ℝ) * intForm a.val (F.eval y) ≤ h.2) ↔
      ((clippingMatrix F B η trueLog).map (Rat.cast : ℚ → ℝ) *ᵥ y) (a,s) ≤
        (clippingRhs F B η trueLog (a,s) : ℝ) := by
    dsimp only
    rw [intForm_eval_eq]
    simp only [clippingMatrix, clippingRhs, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Rat.cast_sub, Rat.cast_mul, mul_add, Finset.mul_sum, mul_assoc, le_sub_iff_add_le]
  constructor
  · intro hall ⟨a,s⟩
    apply (row a s).mp
    apply (ClipRow.holds_iff_halfspaces ..).mp
    apply hall
    rw [abs_sum_cast]; exact_mod_cast a.property
  · intro hall w hw
    rw [abs_sum_cast] at hw
    have hnat : (∑ i, (w i).natAbs) ≤ 4 := by exact_mod_cast hw
    apply (ClipRow.holds_iff_halfspaces ..).mpr
    intro s
    exact (row ⟨w,hnat⟩ s).mpr (hall (⟨w,hnat⟩,s))

/-- No more than four coordinates can enter one signed sum. -/
theorem boundedForm_support_card (a : BoundedForm ι) :
    (Finset.univ.filter fun i => a.val i ≠ 0).card ≤ 4 := by
  let S := Finset.univ.filter fun i => a.val i ≠ 0
  calc
    S.card = ∑ i ∈ S, 1 := by simp
    _ ≤ ∑ i ∈ S, (a.val i).natAbs := by
      apply Finset.sum_le_sum
      intro i hi
      exact Int.natAbs_pos.mpr ((Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, (a.val i).natAbs := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ _ := a.property

/-- Bounds on the magnitudes and denominators of each individual coefficient combine
with a loss depending on four terms only, including for the affine offset. -/
theorem boundedSum_bounds (a : BoundedForm ι) (v : ι → ℚ) {C D : ℕ}
    (hD : 0 < D) (hv : ∀ i, |v i| ≤ (C:ℚ) ∧ (v i).den ≤ D) :
    |boundedSum a v| ≤ 4 * (C:ℚ) ∧ (boundedSum a v).den ≤ D^4 := by
  constructor
  · calc
      |boundedSum a v| ≤ ∑ i, |(a.val i : ℚ) * v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(a.val i : ℚ)| * C := Finset.sum_le_sum fun i _ =>
        (abs_mul ..).le.trans (mul_le_mul_of_nonneg_left (hv i).1 (abs_nonneg _))
      _ = ((∑ i, (a.val i).natAbs : ℕ):ℚ) * C := by
        rw [← Finset.sum_mul, Nat.cast_sum]; simp [Nat.cast_natAbs, Int.cast_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast a.property) (by positivity)
  · let S := Finset.univ.filter fun i => a.val i ≠ 0
    have hsum : boundedSum a v = ∑ i ∈ S, (a.val i:ℚ)*v i := by
      apply Eq.symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have : a.val i = 0 := by simpa [S] using hi
      simp [this]
    rw [hsum]
    have hp : 0 < ∏ i ∈ S, ((a.val i:ℚ)*v i).den := Finset.prod_pos fun i _ => Rat.den_pos _
    calc
      _ ≤ ∏ i ∈ S, ((a.val i:ℚ)*v i).den := Nat.le_of_dvd hp (Finset.Rat.den_sum_dvd_prod_den _ _)
      _ ≤ ∏ _i ∈ S, D := Finset.prod_le_prod fun i _ => by
        have hd : ((a.val i:ℚ)*v i).den ∣ (v i).den := by simpa using Rat.mul_den_dvd (a.val i) (v i)
        exact (Nat.le_of_dvd (Rat.den_pos _) hd).trans (hv i).2
      _ = D^S.card := by simp
      _ ≤ D^4 := Nat.pow_le_pow_right hD (boundedForm_support_card a)

/-- A rational of bounded magnitude and denominator has bounded reduced numerator. -/
theorem numerator_bound_of_abs_den (q : ℚ) {C D : ℕ} (habs : |q| ≤ (C:ℚ))
    (hden : q.den ≤ D) : q.num.natAbs ≤ C*D := by
  have hd : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : ((q.num.natAbs:ℕ):ℚ) / q.den = |q| := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← abs_of_nonneg hd.le, ← abs_div]
    simp [Rat.num_div_den]
  have hle := (div_le_iff₀ hd).mp (hq.trans_le habs)
  exact_mod_cast hle.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hden : (q.den:ℚ) ≤ D) (by positivity))

omit [Fintype κ] in
/-- Height bounds of both the clipping matrix and its right-hand side. The growth
from combining affine expressions depends on the four-term bound, independently of
how many minors there are. `U,E` bound the endpoints of the clipping intervals. -/
theorem clipping_entries_bounds (F : AffineFamily ι κ) (B η : ℚ) (trueLog : ι → ℝ)
    {C D U E : ℕ} (hD : 0 < D)
    (hc : ∀ i j, |F.coefficient i j| ≤ (C:ℚ) ∧ (F.coefficient i j).den ≤ D)
    (ho : ∀ i, |F.offset i| ≤ (C:ℚ) ∧ (F.offset i).den ≤ D)
    (hend : ∀ (a : BoundedForm ι) (s : Bool),
      let e := ((comparisonRow B η (intForm a.val trueLog)).halfspace s).2
      |e| ≤ (U:ℚ) ∧ e.den ≤ E) :
    (∀ t j, (clippingMatrix F B η trueLog t j).num.natAbs ≤ (4*C)*(D^4) ∧
      (clippingMatrix F B η trueLog t j).den ≤ D^4) ∧
    (∀ t, (clippingRhs F B η trueLog t).num.natAbs ≤ (U+4*C)*(E*D^4) ∧
      (clippingRhs F B η trueLog t).den ≤ E*D^4) := by
  have signed (a : BoundedForm ι) (s : Bool) (v : ι → ℚ)
      (hv : ∀ i, |v i| ≤ (C:ℚ) ∧ (v i).den ≤ D) :
      let x := ((comparisonRow B η (intForm a.val trueLog)).halfspace s).1 * boundedSum a v
      |x| ≤ ((4*C:ℕ):ℚ) ∧ x.den ≤ D^4 := by
    dsimp only
    have hb := boundedSum_bounds a v hD hv
    rcases (comparisonRow B η (intForm a.val trueLog)).halfspace_sign s with h | h <;>
      simpa [h] using hb
  constructor
  · intro ⟨a,s⟩ j
    have h := signed a s (fun i => F.coefficient i j) (fun i => hc i j)
    exact ⟨numerator_bound_of_abs_den _ h.1 h.2, h.2⟩
  · intro ⟨a,s⟩
    let e := ((comparisonRow B η (intForm a.val trueLog)).halfspace s).2
    let o := ((comparisonRow B η (intForm a.val trueLog)).halfspace s).1 * boundedSum a F.offset
    have he : |e| ≤ (U:ℚ) ∧ e.den ≤ E := hend a s
    have h₁ : |o| ≤ ((4*C:ℕ):ℚ) ∧ o.den ≤ D^4 := signed a s _ ho
    have h₂ : |e-o| ≤ ((U+4*C:ℕ):ℚ) := by
      calc
        _ ≤ |e|+|o| := abs_sub _ _
        _ ≤ U+(4*C:ℕ) := add_le_add he.1 h₁.1
        _ = _ := by push_cast; rfl
    have h₃ : (e-o).den ≤ E*D^4 :=
      (Nat.le_of_dvd (Nat.mul_pos e.den_pos o.den_pos) (Rat.sub_den_dvd _ _)).trans
        (Nat.mul_le_mul he.2 h₁.2)
    exact ⟨numerator_bound_of_abs_den _ h₂ h₃, h₃⟩

/-- The clipping endpoints on the reciprocal-integer grid have magnitude at most `B+17`
and denominator at most `E`, regardless of the unbounded true logarithmic comparison. -/
theorem comparisonRow_endpoint_bounds (B E : ℕ) (hE : 0 < E) (v : ℝ) (s : Bool) :
    let e := ((comparisonRow (B:ℚ) (1/(E:ℚ)) v).halfspace s).2
    |e| ≤ ((B+17:ℕ):ℚ) ∧ e.den ≤ E := by
  let η : ℚ := 1 / (E:ℚ)
  have he : (0:ℚ) < E := by exact_mod_cast hE
  have he₁ : (1:ℚ) ≤ E := by exact_mod_cast hE
  have hη : 0 < η := div_pos one_pos he
  have hη₁ : η ≤ 1 := (div_le_one he).mpr he₁
  have hηγ : η * E = 1 := div_mul_cancel₀ _ he.ne'
  have denominator (q : ℚ) (z : ℤ) (hz : q * E = z) : q.den ≤ E := by
    rw [(eq_div_iff he.ne').mpr hz, ← Int.cast_natCast E, Rat.intCast_div_eq_divInt]
    exact Nat.le_of_dvd hE (Int.natCast_dvd_natCast.mp (Rat.den_dvd z (E:ℤ)))
  have bound (x : ℚ) (z : ℤ) (hx : |x| ≤ (B:ℚ)+1) (hz : x*E = z) :
      |x+16*η| ≤ ((B+17:ℕ):ℚ) ∧ (x+16*η).den ≤ E := by
    constructor
    · apply (abs_add_le _ _).trans
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hη.le)]; push_cast; linarith
    · apply denominator _ (z+16)
      rw [add_mul, mul_assoc, hηγ, mul_one, hz]; push_cast; rfl
  have ext := bound (-(B:ℚ)) (-(B:ℤ)*E) (by simp) (by push_cast; rfl)
  let w := gridFloor η v
  have hw : w * E = (⌊v/(η:ℝ)⌋ : ℤ) := by
    dsimp only [w, gridFloor]; rw [mul_assoc, hηγ, mul_one]
  change let e := ((comparisonRow (B:ℚ) η v).halfspace s).2; _
  dsimp only
  unfold comparisonRow
  split
  · simpa [η, ClipRow.halfspace, neg_sub, sub_eq_add_neg, add_comm] using ext
  · rename_i hlo
    split
    · simpa [η, ClipRow.halfspace] using ext
    · rename_i hhi
      have hboundR : |(w:ℝ)| ≤ (B:ℝ)+1 := by
        have hg := gridFloor_bounds hη v
        have hηR : (η:ℝ) ≤ 1 := by exact_mod_cast hη₁
        dsimp only [w]
        push_cast at hlo hhi
        exact abs_le.mpr ⟨by linarith [hg.2], by linarith [hg.1]⟩
      have hbound : |w| ≤ (B:ℚ)+1 := by exact_mod_cast hboundR
      cases s
      · have h := bound (-w) (-⌊v/(η:ℝ)⌋) (by simpa using hbound) (by simpa using congrArg Neg.neg hw)
        simpa [η, ClipRow.halfspace, w, neg_sub, sub_eq_add_neg, add_comm] using h
      · simpa [η, ClipRow.halfspace, w] using bound w _ hbound hw

omit [Fintype κ] in
/-- A uniform integer height bound for every entry of the actual rational clipping
system, including the right-hand side, on a reciprocal-integer grid. -/
theorem clipping_system_height (F : AffineFamily ι κ) (B E : ℕ) (trueLog : ι → ℝ)
    {C D : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hc : ∀ i j, |F.coefficient i j| ≤ (C:ℚ) ∧ (F.coefficient i j).den ≤ D)
    (ho : ∀ i, |F.offset i| ≤ (C:ℚ) ∧ (F.offset i).den ≤ D) :
    let H := (B+17+4*C)*(E*D^4)
    let A := clippingMatrix F (B:ℚ) (1/(E:ℚ)) trueLog
    let b := clippingRhs F (B:ℚ) (1/(E:ℚ)) trueLog
    (∀ t j, (A t j).num.natAbs ≤ H ∧ (A t j).den ≤ H) ∧
      (∀ t, (b t).num.natAbs ≤ H ∧ (b t).den ≤ H) := by
  obtain ⟨ha,hb⟩ := clipping_entries_bounds F (B:ℚ) (1/(E:ℚ)) trueLog hD hc ho
    (fun a s => comparisonRow_endpoint_bounds B E hE (intForm a.val trueLog) s)
  have hd : D^4 ≤ E*D^4 := Nat.le_mul_of_pos_left _ hE
  have hu : E*D^4 ≤ (B+17+4*C)*(E*D^4) := Nat.le_mul_of_pos_left _ (by omega)
  constructor
  · intro t j
    obtain ⟨hn, hz⟩ := ha t j
    exact ⟨hn.trans (Nat.mul_le_mul (by omega) hd), hz.trans (hd.trans hu)⟩
  · intro t
    exact ⟨(hb t).1, (hb t).2.trans hu⟩

/-- A reduced numerator bounds the absolute value of a rational. -/
theorem rat_abs_le_num_natAbs (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have hd : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  calc
    |q| = (q.num.natAbs:ℚ) / q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← abs_of_nonneg (by positivity : (0:ℚ) ≤ q.den),
        ← abs_div, Rat.num_div_den]
    _ ≤ _ := div_le_self (by positivity) hd

omit [Fintype ι] in
/-- Evaluating the rational affine data at a point of bounded height gives a simultaneous
magnitude and encoding bound whose only dimension parameter is the number of generators. -/
theorem AffineFamily.evalRat_height (F : AffineFamily ι κ) (y : κ → ℚ) (u : ι)
    {C D H : ℕ} (hc : ∀ j, |F.coefficient u j| ≤ (C:ℚ) ∧ (F.coefficient u j).den ≤ D)
    (ho : |F.offset u| ≤ (C:ℚ) ∧ (F.offset u).den ≤ D)
    (hy : ∀ j, (y j).num.natAbs ≤ H ∧ (y j).den ≤ H) :
    let M := Fintype.card κ * (C*H) + C
    let K := D * (D*H)^(Fintype.card κ)
    |F.evalRat y u| ≤ (M:ℚ) ∧ (F.evalRat y u).num.natAbs ≤ M*K ∧
      (F.evalRat y u).den ≤ K := by
  let v (j : κ) := F.coefficient u j * y j
  have term (j : κ) : |v j| ≤ ((C*H:ℕ):ℚ) ∧ (v j).den ≤ D*H := by
    constructor
    · rw [show v j = _ by rfl, abs_mul, Nat.cast_mul]
      have hyabs : |y j| ≤ (H:ℚ) := (rat_abs_le_num_natAbs _).trans (by exact_mod_cast (hy j).1)
      exact mul_le_mul (hc j).1 hyabs (abs_nonneg _) (by positivity)
    · exact (Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _))
        (Rat.mul_den_dvd _ _)).trans (Nat.mul_le_mul (hc j).2 (hy j).2)
  have hvabs : |∑ j, v j| ≤ ((Fintype.card κ * (C*H):ℕ):ℚ) := calc
    _ ≤ ∑ j, |v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, ((C*H:ℕ):ℚ) := Finset.sum_le_sum fun j _ => (term j).1
    _ = _ := by simp
  have hvden : (∑ j, v j).den ≤ (D*H)^(Fintype.card κ) := calc
    _ ≤ ∏ j, (v j).den := Nat.le_of_dvd (Finset.prod_pos fun _ _ => Rat.den_pos _)
      (Finset.Rat.den_sum_dvd_prod_den _ _)
    _ ≤ ∏ _j : κ, D*H := Finset.prod_le_prod fun j _ => (term j).2
    _ = _ := by simp
  have habs : |F.evalRat y u| ≤ ((Fintype.card κ * (C*H) + C:ℕ):ℚ) :=
    (abs_add_le _ _).trans (by push_cast; simpa using add_le_add hvabs ho.1)
  have hden : (F.evalRat y u).den ≤ D*(D*H)^(Fintype.card κ) := calc
    _ ≤ (∑ j, v j).den * (F.offset u).den := Nat.le_of_dvd
      (Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)) (Rat.add_den_dvd _ _)
    _ ≤ (D*H)^(Fintype.card κ) * D := Nat.mul_le_mul hvden ho.2
    _ = _ := mul_comm ..
  exact ⟨habs, numerator_bound_of_abs_den _ habs hden, hden⟩

end Compression
end LinearProgramming
end Optimization
end OAI
