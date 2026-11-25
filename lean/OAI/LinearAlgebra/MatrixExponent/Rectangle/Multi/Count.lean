import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Perm
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Basic.NNReal.Basic
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord

/-! # The volume correction per variable -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Filter
open scoped Topology

private def volume (n : ℕ) : ℝ := n * Real.log n - Real.log n.factorial

def correction (n : ℕ) := Real.log n - Real.log n.factorial / n

private theorem volume_step (n : ℕ) :
    (n : ℝ) / (n + 1) ≤ volume (n + 1) - volume n ∧ volume (n + 1) - volume n ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [volume]
  have h₀ : 0 < (n : ℝ) := by positivity
  have h₁ : 0 < (n : ℝ) + 1 := by positivity
  have he : volume (n + 1) - volume n = (n : ℝ) * (Real.log (n + 1) - Real.log n) := by
    unfold volume
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.log_mul h₁.ne' (by positivity)]
    ring
  rw [he]
  have hl := Real.log_le_sub_one_of_pos (div_pos h₀ h₁)
  have hu := Real.log_le_sub_one_of_pos (div_pos h₁ h₀)
  rw [Real.log_div h₀.ne' h₁.ne', show (n : ℝ) / (n + 1) - 1 = -1 / (n + 1) by field_simp; ring, neg_div] at hl
  rw [Real.log_div h₁.ne' h₀.ne', add_div, div_self h₀.ne', add_sub_cancel_left] at hu
  constructor
  · rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by rw [one_div] at hl; linarith) h₀.le
  · rw [mul_comm, ← le_div_iff₀ h₀]
    exact hu

theorem correction_le (n : ℕ) : correction n ≤ 1 := by
  have h (m : ℕ) : volume m ≤ m := by
    induction m with
    | zero => simp [volume]
    | succ m ih => rw [Nat.cast_succ]; linarith [(volume_step m).2]
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [correction]
  have he := h n
  unfold volume at he
  unfold correction
  field_simp
  linarith

theorem correction_limit : Tendsto correction atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have h := (tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
    (fun n => (volume_step n).1) (fun n => (volume_step n).2)).cesaro
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Finset.sum_range_sub]
  unfold volume correction
  simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one, Real.log_one, zero_mul, sub_zero]
  field_simp

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-! The sum of all positive pair differences is subadditive.
For vectors with distinct entries equality forces a common ordering. -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Finset

variable {m : ℕ} {ι : Type} [Fintype ι]

private def support (q : Equiv.Perm (Fin m)) (x : Fin m → ℤ) (p : Fin m × Fin m) :=
  if q p.1 < q p.2 then x p.2 - x p.1 else 0

def variation (x : Fin m → ℤ) := ∑ p : Fin m × Fin m, max (x p.2 - x p.1) 0

private theorem support_le (q : Equiv.Perm (Fin m)) (x : Fin m → ℤ) (p : Fin m × Fin m) :
    support q x p ≤ max (x p.2 - x p.1) 0 := by
  unfold support
  split <;> simp

private theorem support_eq (p q : Equiv.Perm (Fin m)) (x : Fin m → ℤ)
    (hx : ∀ a b, x a < x b ↔ p a < p b) :
    (∑ u, support q x u) = variation x ↔ p = q := by
  rw [variation, sum_eq_sum_iff_of_le (fun u _ => support_le q x u)]
  constructor
  · intro he
    have hm : StrictMono (fun i => q (p.symm i)) := by
      intro a b hab
      have h := he (p.symm a, p.symm b) (mem_univ _)
      have h' : x (p.symm a) < x (p.symm b) := (hx _ _).mpr (by simpa using hab)
      by_contra! hc
      simp [support, not_lt.mpr hc] at h
      omega
    apply Equiv.ext
    intro a
    simpa using (congrFun hm.eq_id (p a)).symm
  · rintro rfl u _
    simp only [support, ← hx]
    split <;> omega

theorem variation_rule (p : Option ι → Equiv.Perm (Fin m)) (x : Option ι → Fin m → ℤ)
    (hx : ∀ s a b, x s a < x s b ↔ p s a < p s b)
    (he : ∀ a, ∑ i, x (some i) a = x none a) :
    variation (x none) ≤ ∑ i, variation (x (some i)) ∧
      (variation (x none) = ∑ i, variation (x (some i)) ↔ ∀ i, p (some i) = p none) := by
  have hr : variation (x none) = ∑ i, ∑ u, support (p none) (x (some i)) u := by
    rw [← (support_eq _ _ _ (hx none)).mpr rfl, sum_comm]
    refine sum_congr rfl fun u _ => ?_
    unfold support
    split <;> simp [*, sum_sub_distrib]
  have hl i : (∑ u, support (p none) (x (some i)) u) ≤ variation (x (some i)) :=
    sum_le_sum fun u _ => support_le _ _ u
  rw [hr]
  refine ⟨sum_le_sum fun i _ => hl i, ?_⟩
  simp only [sum_eq_sum_iff_of_le (fun i _ => hl i), mem_univ, forall_true_left,
    support_eq _ _ _ (hx _)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-! Multivariate polynomial multiplication with total-degree budgets. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

abbrev Deg (m d : ℕ) := {x : Fin m → ℕ // ∑ i, x i ≤ d}

instance (m d : ℕ) : Fintype (Deg m d) := by
  classical
  let f (x : Deg m d) (i : Fin m) : Fin (d + 1) :=
    ⟨x.val i, Nat.lt_succ_of_le ((single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans x.property)⟩
  exact Fintype.ofInjective f (fun x y h => Subtype.ext (funext fun i => congrArg Fin.val (congrFun h i)))

variable {ι : Type} [Fintype ι]

abbrev leg (m : ℕ) (L : ι → ℕ) (s : Option ι) := Deg m (Profile.length L s)

variable (F : Type) [Field F] (m : ℕ) (L : ι → ℕ)

def entry (x : ∀ s, leg m L s) : F := if ∑ i, (x (some i)).val = (x none).val then 1 else 0

def simplex : Tensor F (Option ι) := Tensor.ofRaw (Raw.ofTable (leg m L) (entry F m L))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# Homogeneous coordinates on a simplex

A slack variable gives each monomial a prescribed total degree.
A pair of multiplications has one term for each pair of input tuples.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

abbrev Letter (m : ℕ) := Option (Fin m)
abbrev Word (m d : ℕ) := Sym (Letter m) d

variable {m d : ℕ}

private theorem size (t : Multiset (Letter m)) :
    t.count none + ∑ i, t.count (some i) = t.card := by
  rw [← Fintype.sum_option (fun i => t.count i),
    Multiset.sum_count_eq_card (fun _ _ => mem_univ _)]

private theorem ext_word {t u : Multiset (Letter m)} (hd : t.card = u.card) :
    t = u ↔ ∀ i, t.count (some i) = u.count (some i) := by
  refine ⟨fun h => by rw [h]; simp, fun h => Multiset.ext.mpr ?_⟩
  rintro (_ | i)
  · have ht := size t
    have hu := size u
    simp_rw [h] at ht
    omega
  · exact h i

private def unpad (t : Word m d) : Deg m d :=
  ⟨fun i => t.val.count (some i),
    (Nat.le_add_left _ _).trans_eq ((size t.val).trans t.property)⟩

def coordinates (m d : ℕ) : Word m d ≃ Deg m d := Equiv.ofBijective unpad (by
  constructor
  · intro t u h
    exact Subtype.ext ((ext_word (t.property.trans u.property.symm)).mpr
      (fun i => congrFun (congrArg Subtype.val h) i))
  · intro x
    let t := Multiset.replicate (d - ∑ i, x.val i) none +
      ∑ i, Multiset.replicate (x.val i) (some i)
    have he : t.card = d := by
      simp only [t, Multiset.card_add, Multiset.card_sum, Multiset.card_replicate]
      exact Nat.sub_add_cancel x.property
    refine ⟨⟨t, he⟩, Subtype.ext (funext fun i => ?_)⟩
    simp [unpad, t, Multiset.count_replicate, Multiset.count_sum'])

variable {ι : Type} [Fintype ι] (L R : ι → ℕ)

def merge (x : ∀ i, Word m (L i)) : Word m (∑ i, L i) :=
  ⟨∑ i, (x i).val, by rw [Multiset.card_sum]; exact sum_congr rfl fun i _ => (x i).property⟩

private theorem merge_eq (x : ∀ s, Word m (Profile.length L s)) :
    merge L (fun i => x (some i)) = x none ↔
      ∑ i, (unpad (x (some i))).val = (unpad (x none)).val := by
  erw [Subtype.ext_iff, ext_word ((merge L _).property.trans (x none).property.symm)]
  simp only [merge, Multiset.count_sum', unpad, funext_iff, Finset.sum_apply]

abbrev Both (m : ℕ) (s : Option ι) := Word m (Profile.length L s) × Word m (Profile.length R s)
abbrev Inputs (m : ℕ) := ∀ i, Both L R m (some i)

def extend (x : Inputs L R m) : ∀ s, Both L R m s
  | some i => x i
  | none => (merge L (fun i => (x i).1), merge R (fun i => (x i).2))

variable (F : Type) [Field F] (m) [DecidableEq ι]

def double : Raw F (Option ι) :=
  ⟨Both L R m, Inputs L R m, fun x s y => if extend L R x s = y then 1 else 0⟩

theorem double_coeff (x : ∀ s, Both L R m s) :
    (double m L R F).coeff x =
      if extend L R (fun i => x (some i)) none = x none then 1 else 0 := by
  classical
  change ∑ y : Inputs L R m, ∏ s, (if extend L R y s = x s then (1 : F) else 0) = _
  rw [Fintype.sum_eq_single (fun i => x (some i))]
  · rw [Fintype.prod_option]
    simp [extend]
  · intro y hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact prod_eq_zero (mem_univ (some i)) (ite_eq_right hi)

theorem double_eq : Tensor.ofRaw (double m L R F) = simplex F m L * simplex F m R := by
  unfold simplex
  rw [← Tensor.ofRaw_mul]
  let e s := (coordinates m (Profile.length L s)).prodCongr (coordinates m (Profile.length R s))
  refine Tensor.ofRaw_eq (Raw.equiv_coeff e fun x => ?_)
  change (∀ s, Both L R m s) at x
  erw [double_coeff, Raw.coeff_mul, Raw.coeff_ofTable, Raw.coeff_ofTable]
  change _ = entry F m L (fun s => unpad (x s).1) * entry F m R (fun s => unpad (x s).2)
  simp only [entry, ite_mul, one_mul, zero_mul, ← ite_and]
  congr 1
  exact propext (Prod.ext_iff.trans (and_congr (merge_eq L (fun s => (x s).1))
    (merge_eq R (fun s => (x s).2))))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-! # Number of available cube translations in a degree simplex -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Finset

theorem count_lower (m q : ℕ) : q ^ m ≤ m.factorial * Fintype.card (Deg m q) := by
  have h := (Fintype.card_congr (coordinates m q)).le
  change Fintype.card (Sym (Option (Fin m)) q) ≤ Fintype.card (Deg m q) at h
  rw [Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_fin,
    show m + 1 + q - 1 = q + m by omega, Nat.choose_symm_add] at h
  calc
    _ ≤ (q + 1) ^ m := Nat.pow_le_pow_left (by omega) _
    _ ≤ (q + 1).ascFactorial m := Nat.pow_succ_le_ascFactorial _ _
    _ = m.factorial * (q + m).choose m := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ _ := Nat.mul_le_mul_left _ h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# Bihomogeneous substitution

Expand `X^u (X+Y)^v` in powers of `X+Y` and `Y`. Its component of
highest Y-degree is `X^u Y^v`. Terms already containing too many Y's
cannot contribute to the chosen component.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Finset

abbrev Mon (m : ℕ) := Multiset (Letter m)
abbrev Poly (F : Type) [Field F] (m : ℕ) := AddMonoidAlgebra F (Mon m × Mon m)

variable (F : Type) [Field F] {m : ℕ}

private def mon (u v : Mon m) : Poly F m := AddMonoidAlgebra.single (u, v) 1

/-- The monomial `X^u Y^v (X+Y)^w` in a formal polynomial ring. -/
def mix (u v w : Mon m) : Poly F m :=
  mon F u v * (w.map fun i => mon F {i} 0 + mon F 0 {i}).prod

private theorem mon_mul (u v p q : Mon m) : mon F u v * mon F p q = mon F (u + p) (v + q) := by
  simp [mon]

private theorem mix_mul (u v w a b c : Mon m) :
    mix F u v w * mix F a b c = mix F (u + a) (v + b) (w + c) := by
  unfold mix
  rw [mul_mul_mul_comm, mon_mul, Multiset.map_add, Multiset.prod_add]

theorem mix_prod {ι : Type} (s : Finset ι) (u v w : ι → Mon m) :
    ∏ i ∈ s, mix F (u i) (v i) (w i) = mix F (∑ i ∈ s, u i) (∑ i ∈ s, v i) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mix, mon, AddMonoidAlgebra.one_def]; rfl
  | insert i s hi ih => simp only [prod_insert hi, sum_insert hi, ih, mix_mul]

private theorem mix_cons (u v w : Mon m) (i : Letter m) :
    mix F u v (i ::ₘ w) = mix F (i ::ₘ u) v w + mix F u (i ::ₘ v) w := by
  unfold mix
  rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc, mul_add, add_mul,
    mul_comm (mon F u v) (mon F _ _), mon_mul, mul_comm (mon F u v) (mon F _ _), mon_mul]
  simp

theorem mix_high (u v w p q : Mon m) (h : v.card + w.card ≤ q.card) :
    (mix F u v w).coeff (p, q) = if (u, v + w) = (p, q) then 1 else 0 := by
  induction w using Multiset.induction_on generalizing u v with
  | empty => simp [mix, mon, Finsupp.single_apply]
  | cons i w ih =>
    have hne : (i ::ₘ u, v + w) ≠ (p, q) := by
      intro he
      have he' := congrArg (fun z => z.2.card) he
      simp at he' h
      omega
    rw [mix_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih, ih, ite_eq_right hne, zero_add]
    · simp
    all_goals simp at h ⊢; omega

theorem mix_low (u v w p q : Mon m) (h : q.card < v.card) :
    (mix F u v w).coeff (p, q) = 0 := by
  induction w using Multiset.induction_on generalizing u v with
  | empty =>
    have : v ≠ q := by rintro rfl; exact lt_irrefl _ h
    simp [mix, mon, this]
  | cons i w ih =>
    rw [mix_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih _ _ h, ih, add_zero]
    simp; omega

abbrev Part (m a b : ℕ) (t : Fin (a + 1)) := Word m (a + b - t.val) × Word m t.val

/-- The new right degree can be at most the old left degree. -/
theorem expand_mix {a b : ℕ} (x : Word m a) (y : Word m b) :
    ∃ c : ∀ t : Fin (a + 1), Part m a b t → F,
      ∑ t, ∑ z, c t z • mix F 0 z.2.val z.1.val = mix F x.val 0 y.val := by
  classical
  let B (z : Σ t : Fin (a + 1), Part m a b t) := mix F 0 z.2.2.val z.2.1.val
  let W := Submodule.span F (Set.range B)
  have h (u v w : Mon m) (hu : u.card + v.card ≤ a) (hw : u.card + v.card + w.card = a + b) :
      mix F u v w ∈ W := by
    induction u using Multiset.induction_on generalizing v w with
    | empty =>
      simp only [Multiset.card_zero, zero_add] at hu hw
      let t : Fin (a + 1) := ⟨v.card, by omega⟩
      let z : Part m a b t := (⟨w, by dsimp [t]; omega⟩, ⟨v, rfl⟩)
      exact Submodule.subset_span ⟨⟨t, z⟩, rfl⟩
    | cons i u ih =>
      have h₁ : mix F u v (i ::ₘ w) ∈ W := ih _ _ (by simp at hu; omega) (by simp at hw ⊢; omega)
      have h₂ : mix F u (i ::ₘ v) w ∈ W := ih _ _ (by simp at hu ⊢; omega) (by simp at hw ⊢; omega)
      rw [mix_cons] at h₁
      exact (W.add_mem_iff_left h₂).mp h₁
  have he := h x.val 0 y.val (by simp) (by simp)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp he
  refine ⟨fun t z => c ⟨t, z⟩, ?_⟩
  rw [Fintype.sum_sigma] at hc
  exact hc

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# Redistributing degree budgets

At each input expand in the variables `X+Y,Y`. At the output extract
the coefficient with the original Y-degree. Sectors above that degree
vanish. Each remaining sector is a pair of ordinary multiplications.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset
open scoped NNReal

variable {ι F : Type} [Fintype ι] [Field F] {m : ℕ}

private abbrev Slot (L : ι → ℕ) := ∀ i, Fin (L i + 1)
private abbrev left {L : ι → ℕ} (R : ι → ℕ) (t : Slot L) (i : ι) := L i + R i - (t i).val
private abbrev right {L : ι → ℕ} (t : Slot L) (i : ι) := (t i).val

private def old (F : Type) [Field F] {a b : ℕ} (z : Word m a × Word m b) :=
  mix F z.1.val 0 z.2.val

private def new (F : Type) [Field F] {a b : ℕ} (z : Word m a × Word m b) :=
  mix F 0 z.2.val z.1.val

private def changeVar (F : Type) [Field F] {a b : ℕ} (z : Word m a × Word m b) :=
  (expand_mix F z.1 z.2).choose

private theorem changeVar_spec {a b : ℕ} (z : Word m a × Word m b) :
    old F z = ∑ t, ∑ y, changeVar F z t y • new F y :=
  (expand_mix F z.1 z.2).choose_spec.symm

private def read (F : Type) [Field F] {a b : ℕ} (z : Word m a × Word m b) : Poly F m →ₗ[F] F :=
  (Finsupp.lapply (z.1.val, z.2.val)).comp (AddMonoidAlgebra.coeffLinearEquiv F).toLinearMap

private theorem read_old {a b : ℕ} (z y : Word m a × Word m b) :
    read F z (old F y) = if y = z then 1 else 0 := by
  change (mix F y.1.val 0 y.2.val).coeff (z.1.val, z.2.val) = _
  rw [mix_high _ _ _ _ _ _ (by simp), zero_add]
  congr 1
  exact propext (Prod.ext_iff.trans ((and_congr Subtype.ext_iff.symm Subtype.ext_iff.symm).trans Prod.ext_iff.symm))

private theorem read_new {a b c d : ℕ} (z : Word m a × Word m b) (y : Word m c × Word m d)
    (h : b < d) : read F z (new F y) = 0 :=
  mix_low F 0 y.2.val y.1.val z.1.val z.2.val (by simpa using h)

variable (L R : ι → ℕ)

private theorem old_prod (x : Inputs L R m) :
    ∏ i, old F (x i) = old F (extend L R x none) := by
  unfold old
  rw [mix_prod, sum_const_zero]
  rfl

private theorem new_prod (x : Inputs L R m) :
    ∏ i, new F (x i) = new F (extend L R x none) := by
  unfold new
  rw [mix_prod, sum_const_zero]
  rfl

variable [DecidableEq ι]

private theorem expand_prod (x : Inputs L R m) :
    old F (extend L R x none) =
      ∑ t : Slot L, ∑ y : Inputs (left R t) (right t) m,
        (∏ i, changeVar F (x i) (t i) (y i)) • new F (extend (left R t) (right t) y none) := by
  rw [← old_prod]
  simp_rw [changeVar_spec]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun y _ => ?_
  change Slot L at t
  change Inputs (left R t) (right t) m at y
  erw [← new_prod (left R t) (right t) y]
  simp only [Algebra.smul_def, prod_mul_distrib, map_prod]
  rfl

private def maps (t : Slot L) : Raw.Local (double m (left R t) (right t) F) (double m L R F)
  | none, x, y => read F x (new F y)
  | some i, x, y => changeVar F x (t i) y

private theorem apply_maps (t : Slot L) (x : ∀ s, Both L R m s) :
    (double m (left R t) (right t) F).applyLocal (maps L R t) x =
      ∑ y : Inputs (left R t) (right t) m,
        (∏ i, changeVar F (x (some i)) (t i) (y i)) *
          read F (x none) (new F (extend (left R t) (right t) y none)) := by
  unfold Raw.applyLocal
  refine sum_congr rfl fun y _ => ?_
  change Inputs (left R t) (right t) m at y
  change (∏ s, ∑ z : Both (left R t) (right t) m s,
    maps L R t s (x s) z * if extend (left R t) (right t) y s = z then 1 else 0) = _
  have hs s : (∑ z : Both (left R t) (right t) m s,
      maps (F := F) L R t s (x s) z * if extend (left R t) (right t) y s = z then 1 else 0) =
      maps L R t s (x s) (extend (left R t) (right t) y s) := by
    rw [Fintype.sum_eq_single (extend (left R t) (right t) y s)]
    · simp
    · intro z hz
      simp [hz.symm]
  simp_rw [hs]
  rw [Fintype.prod_option, mul_comm]
  rfl

private def sectors := (univ : Finset (Slot L)).filter (fun t => ∑ i, right t i ≤ ∑ i, R i)

private theorem redistribution :
    Tensor.ofRaw (double m L R F) ≤
      ∑ t ∈ sectors L R, Tensor.ofRaw (double m (left R t) (right t) F) := by
  refine (Raw.restriction_sum_iff _ _ _).mpr ⟨maps L R, fun x => ?_⟩
  change (∀ s, Both L R m s) at x
  have hfull : (double m L R F).coeff x =
      ∑ t : Slot L, (double m (left R t) (right t) F).applyLocal (maps L R t) x := by
    rw [double_coeff, ← read_old, expand_prod L R]
    simp only [map_sum, map_smul, smul_eq_mul, apply_maps]
  rw [hfull]
  symm
  apply sum_subset (subset_univ _)
  intro t _ ht
  have he : (∑ i, R i) < ∑ i, right t i := by simpa [sectors] using ht
  rw [apply_maps]
  apply sum_eq_zero
  intro y _
  exact mul_eq_zero_of_right _ (read_new _ _ he)

private theorem card_sectors :
    (sectors L R).card ≤ (1 + ∑ i, (L i + R i)) ^ Fintype.card ι := by
  calc
    _ ≤ Fintype.card (Slot L) := card_le_univ _
    _ = ∏ i, (L i + 1) := by simp [Slot, Fintype.card_pi]
    _ ≤ ∏ _i : ι, (1 + ∑ i, (L i + R i)) := by
      apply prod_le_prod
      intro i hi
      have h := single_le_sum (f := fun i => L i + R i) (fun _ _ => Nat.zero_le _) hi
      omega
    _ = _ := by simp

/-- The number of bidegree sectors is polynomial in the total degree. -/
theorem sector (s : Finset ι) (hs : ∀ i ∈ s, L i = 0)
    (f : Tensor F (Option ι) →+* NNReal) (hf : Monotone f) :
    ∃ U V : ι → ℕ, U + V = L + R ∧ (∀ i ∈ s, V i = 0) ∧ (∑ i, V i) ≤ ∑ i, R i ∧
      f (simplex F m L) * f (simplex F m R) ≤
        ((1 + ∑ i, (L i + R i) : ℕ) : NNReal) ^ Fintype.card ι *
          f (simplex F m U) * f (simplex F m V) := by
  have he : (sectors L R).Nonempty := ⟨fun _ => 0, by simp [sectors, right]⟩
  let g (t : Slot L) := f (Tensor.ofRaw (double m (left R t) (right t) F))
  obtain ⟨t, ht, hmax⟩ := exists_max_image (sectors L R) g he
  refine ⟨left R t, right t, ?_, ?_, (mem_filter.mp ht).2, ?_⟩
  · funext i
    simp only [Pi.add_apply, left, right]
    have := (t i).isLt
    omega
  · intro i hi
    have := (t i).isLt
    have := hs i hi
    unfold right
    omega
  rw [mul_assoc, ← map_mul, ← map_mul, ← double_eq, ← double_eq]
  calc
    _ ≤ ∑ u ∈ sectors L R, g u := by
      rw [← map_sum]
      exact hf (redistribution L R)
    _ ≤ (sectors L R).card * g t := by
      simpa using sum_le_sum (fun u hu => hmax u hu)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_sectors L R) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-! # Natural-log simplex prices at finite placements -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral

variable {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {X : Type*} [PseudoMetricSpace X]

def sites (o : X) (x : ι → X) : Option ι → X := fun i => i.elim o x

def H (A : MatrixExponent.Prices.Atlas K X) (o : X) (x : ι → X) (m : ℕ) (L : ι → ℕ) : ℝ :=
  Real.log 2 * A.price (sites o x) (simplex K m L)

theorem monotone_price [Nontrivial ι] (A : MatrixExponent.Prices.Atlas K X) (x : ι → X) :
    Monotone (A.price x) := by
  obtain ⟨_, d, hd, f, hf, he⟩ := A.valid x
  rw [he]
  intro B T h
  by_cases hb : B = 0
  · simpa [hb, Tensor.values] using Tensor.values_nonneg hd.1 hf T
  unfold Tensor.values
  apply mul_le_mul_of_nonneg_left _ hd.1
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  exact Real.log_le_log (zero_lt_one.trans_le (Tensor.value_one_le hf hb)) (hf h)

theorem H_chord (A : MatrixExponent.Prices.Atlas K X) (o : X) (x y z : ι → X) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h₁ : ∀ i, Dist.dist (x i) (z i) = t * Dist.dist (x i) (y i))
    (h₂ : ∀ i, Dist.dist (z i) (y i) = (1 - t) * Dist.dist (x i) (y i)) (m : ℕ) (L : ι → ℕ) :
    H A o z m L ≤ (1 - t) * H A o x m L + t * H A o y m L := by
  have h := A.chord (x := sites o x) (y := sites o y) (z := sites o z) ht ht'
    (by rintro (_|i); · simp [sites]
        exact h₁ i)
    (by rintro (_|i); · simp [sites]
        exact h₂ i) (simplex K m L)
  unfold H
  linarith only [mul_le_mul_of_nonneg_left h (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# Merging polynomial inputs at each site

Inputs grouped at a site multiply locally. Those reaching the output
site multiply into the answer there. The local coefficient maps use
total degrees, so the new budgets are the sums at the input sites.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (m : ℕ) (L : ι → ℕ) (f : ι → Option κ)

def route (s : Option ι) := s.elim none f

def gather {G : Type*} [AddCommMonoid G] (g : ι → G) (s : Option κ) : G :=
  ∑ i, if f i = s then g i else 0

def merged (j : κ) := gather f L (some j)

omit [DecidableEq ι] in
private theorem gather_all {G : Type*} [AddCommMonoid G] (g : ι → G) :
    gather f g none + ∑ j, gather f g (some j) = ∑ i, g i := by
  rw [← Fintype.sum_option]
  unfold gather
  rw [sum_comm]
  simp

private abbrev Tuple (m : ℕ) (L : ι → ℕ) := ∀ s, leg m L s

private def total {m : ℕ} (v : Fin m → ℕ) : ℕ := ∑ i, v i

omit [DecidableEq ι] in
private theorem total_sum (g : ι → Fin m → ℕ) : total (∑ i, g i) = ∑ i, total (g i) := by
  simp only [total, Finset.sum_apply]
  exact sum_comm

private def collect (x : Tuple m L) : Tuple m (merged L f) := by
  let y j := gather f (fun i => (x (some i)).val) (some j)
  have hy j : total (y j) ≤ merged L f j := by
    unfold y merged gather
    rw [total_sum]
    refine sum_le_sum fun i _ => ?_
    split
    · exact (x (some i)).property
    · simp [total]
  exact fun s => match s with
    | some j => ⟨y j, hy j⟩
    | none => ⟨∑ j, y j, (total_sum _ _).le.trans (sum_le_sum (fun j _ => hy j))⟩

private abbrev Bundle (s : Option κ) := ∀ t : Raw.Fiber (route f) s, leg m L t

private def localSum (s : Option κ) (x : Bundle m L f s) : Fin m → ℕ :=
  ∑ i, if h : f i = s then (x ⟨some i, h⟩).val else 0

private def unbundle (x : ∀ s, Bundle m L f s) : Tuple m L := fun t => x (route f t) ⟨t, rfl⟩

omit [DecidableEq ι] [Fintype κ] in
private theorem localSum_eq (x : ∀ s, Bundle m L f s) (s : Option κ) :
    localSum m L f s (x s) = gather f (fun i => (unbundle m L f x (some i)).val) s := by
  unfold localSum gather
  refine sum_congr rfl fun i _ => ?_
  by_cases he : f i = s
  · subst s
    simp only [↓reduceDIte, ↓reduceIte]
    rfl
  · simp only [he, ↓reduceDIte, ↓reduceIte]

private def fits : (s : Option κ) → Bundle m L f s → leg m (merged L f) s → Prop
  | some j, x, y => y.val = localSum m L f (some j) x
  | none, x, y => localSum m L f none x + y.val = (x ⟨none, rfl⟩).val

omit [DecidableEq ι] in
private theorem valid (x : ∀ s, Bundle m L f s) (y : Tuple m (merged L f)) :
    ((∀ s, fits m L f s (x s) (y s)) ∧ ∑ j, (y (some j)).val = (y none).val) ↔
      y = collect m L f (unbundle m L f x) ∧
        ∑ i, (unbundle m L f x (some i)).val = (unbundle m L f x none).val := by
  let Y := collect m L f (unbundle m L f x)
  have he (j) : (Y (some j)).val = localSum m L f (some j) (x (some j)) :=
    (localSum_eq m L f x _).symm
  have hy : ∑ j, (Y (some j)).val = (Y none).val := rfl
  have hh : localSum m L f none (x none) + (Y none).val =
      ∑ i, (unbundle m L f x (some i)).val := by
    rw [localSum_eq]
    exact gather_all _ _
  constructor
  · rintro ⟨h, hs⟩
    have h' (j) : y (some j) = Y (some j) := Subtype.ext ((h (some j)).trans (he j).symm)
    have hz : y none = Y none := Subtype.ext (by simpa only [h', hy] using hs.symm)
    refine ⟨funext fun s => ?_, hh.symm.trans ?_⟩
    · cases s with
      | none => exact hz
      | some j => exact h' j
    · rw [← hz]
      exact h none
  · rintro ⟨rfl, h⟩
    exact ⟨fun s => match s with | none => hh.trans h | some j => he j, hy⟩

theorem simplex_merge : Tensor.place (route f) (simplex K m L) ≤ simplex K m (merged L f) := by
  classical
  let A := Raw.ofTable (leg m (merged L f)) (entry K m (merged L f))
  let B := (Raw.ofTable (leg m L) (entry K m L)).group (route f)
  let Q s (x : Bundle m L f s) (y : leg m (merged L f) s) : K := if fits m L f s x y then 1 else 0
  apply (Raw.restricts_iff A B).mpr
  refine ⟨Q, fun x => ?_⟩
  change (∀ s, Bundle m L f s) at x
  have hA (y : Tuple m (merged L f)) : A.coeff y = entry K m (merged L f) y := Raw.coeff_ofTable _ _ y
  have hB : B.coeff x = entry K m L (unbundle m L f x) :=
    (Raw.coeff_group _ _ _).trans (Raw.coeff_ofTable _ _ _)
  rw [hB]
  change _ = ∑ y : Tuple m (merged L f), (∏ s, Q s (x s) (y s)) * A.coeff y
  simp only [Q, hA, entry, Fintype.prod_ite_zero, prod_const_one, ite_mul, one_mul,
    zero_mul, ← ite_and, valid m L f x]
  simp only [ite_and, Fintype.sum_ite_eq']

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-! # Zero-degree inputs are dummy sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (m : ℕ) (L : ι → ℕ) (e : ι ↪ κ)

private theorem deg_zero {d : ℕ} (x : Deg m d) (hd : d = 0) : x.val = 0 := by
  funext i
  have := (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans x.property
  change x.val i = 0
  omega

theorem simplex_embed :
    Tensor.place (route (some ∘ e)) (simplex K m L) = simplex K m (merged L (some ∘ e)) := by
  classical
  let M := merged L (some ∘ e)
  let f := route (some ∘ e)
  have hm (s) : Profile.length M (f s) = Profile.length L s := by
    cases s with
    | none =>
      simp only [f, route, Option.elim_none, Profile.length, M, merged, gather]
      rw [sum_comm]
      simp
    | some i => simp [f, route, Profile.length, M, merged, gather, e.injective.eq_iff]
  apply le_antisymm (simplex_merge m L _)
  let A := (Raw.ofTable (leg m L) (entry K m L)).group f
  let lift (t : Option κ) (x : leg m M t) : A.leg t := fun s =>
    ⟨x.val, x.property.trans_eq (by rw [← hm s.val, s.property])⟩
  refine Raw.Restricts.pullback lift fun x => ?_
  change (∀ s, leg m M s) at x
  have hzero {j} (hj : j ∉ univ.map e) : (x (some j)).val = 0 := by
    apply deg_zero
    have hne (i) : e i ≠ j := fun h => hj (mem_map.mpr ⟨i, mem_univ _, h⟩)
    simp [Profile.length, M, merged, gather, hne]
  have he : ∑ j, (x (some j)).val = ∑ i, (x (some (e i))).val := by
    rw [← sum_map univ e (fun j => (x (some j)).val)]
    exact (sum_subset (subset_univ _) (fun _ _ hj => hzero hj)).symm
  erw [Raw.coeff_ofTable, Raw.coeff_group, Raw.coeff_ofTable]
  change (if ∑ j, (x (some j)).val = (x none).val then (1 : K) else 0) =
    if ∑ i, (x (some (e i))).val = (x none).val then 1 else 0
  rw [he]

variable {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X)

private theorem embedded_H (x : κ → X) :
    H A o x m (merged L (some ∘ e)) = H A o (x ∘ e) m L := by
  have hv : sites o (x ∘ e) = sites o x ∘ route (some ∘ e) := by
    funext s
    cases s <;> rfl
  rw [H, H, hv, A.place, Function.comp_apply, simplex_embed]

theorem left_H (x : ι → X) (y : κ → X) :
    H A o (Sum.elim x y) m (Sum.elim L 0) = H A o x m L := by
  let e : ι ↪ ι ⊕ κ := ⟨Sum.inl, Sum.inl_injective⟩
  have he : merged L (some ∘ e) = Sum.elim L 0 := by
    funext s
    rcases s with i | j <;> simp [merged, gather, e]
  rw [← he, embedded_H]
  rfl

theorem right_H (x : κ → X) (y : ι → X) :
    H A o (Sum.elim x y) m (Sum.elim 0 L) = H A o y m L := by
  let e : ι ↪ κ ⊕ ι := ⟨Sum.inr, Sum.inr_injective⟩
  have he : merged L (some ∘ e) = Sum.elim (0 : κ → ℕ) L := by
    funext s
    rcases s with i | j <;> simp [merged, gather, e]
  rw [← he, embedded_H]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# Moving inputs toward the output

Convexity rounds each intermediate placement to one endpoint of its
segment without decreasing the price minus the assigned costs. Merging
inputs then gives a degree budget on the original set of sites.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X)

omit [DecidableEq ι] in
private theorem merged_cost (L : ι → ℕ) (r : ι → Option κ) (f : κ → ℝ) :
    ∑ j, f j * merged L r j = ∑ i, (r i).elim 0 f * L i := by
  simp only [merged, gather, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  cases r i <;> simp

private theorem merge_price [Nonempty κ] (x : κ → X) (m : ℕ) (L : ι → ℕ) (r : ι → Option κ) :
    H A o (fun i => (r i).elim o x) m L ≤ H A o x m (merged L r) := by
  have he : sites o (fun i => (r i).elim o x) = sites o x ∘ route r := by
    funext s
    cases s <;> rfl
  unfold H
  rw [he, A.place, Function.comp_apply]
  exact mul_le_mul_of_nonneg_left (monotone_price A _ (simplex_merge m L r))
    (Real.log_pos (by norm_num)).le

private theorem round_sites (x y : ι → X) (f g t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1)
    (h₁ : ∀ i, Dist.dist o (y i) = t i * Dist.dist o (x i))
    (h₂ : ∀ i, Dist.dist (y i) (x i) = (1 - t i) * Dist.dist o (x i))
    (hg : ∀ i, t i * f i ≤ g i) (m : ℕ) (L : ι → ℕ) :
    ∃ b : ι → Bool, H A o y m L - ∑ i, g i * L i ≤
      H A o (fun i => if b i then x i else o) m L - ∑ i, (if b i then f i else 0) * L i := by
  let p (b : ι → Option Bool) i := (b i).elim (y i) (fun a => if a then x i else o)
  let c (b : ι → Option Bool) i := (b i).elim (g i) (fun a => if a then f i else 0)
  let V b := H A o (p b) m L - ∑ i, c b i * L i
  have step (b : ι → Option Bool) i (hi : b i = none) :
      ∃ a : Bool, V b ≤ V (Function.update b i (some a)) := by
    let l := Function.update b i (some false)
    let r := Function.update b i (some true)
    have hl j : Dist.dist (p l j) (p b j) = t i * Dist.dist (p l j) (p r j) := by
      by_cases h : j = i
      · subst j; simpa [p, l, r, hi] using h₁ i
      · simp [p, l, r, h]
    have hr j : Dist.dist (p b j) (p r j) = (1 - t i) * Dist.dist (p l j) (p r j) := by
      by_cases h : j = i
      · subst j; simpa [p, l, r, hi] using h₂ i
      · simp [p, l, r, h]
    have hc j : (1 - t i) * c l j + t i * c r j ≤ c b j := by
      by_cases h : j = i
      · subst j; simpa [c, l, r, hi] using hg i
      · simp only [c, l, r, Function.update_of_ne h]
        exact le_of_eq (by ring)
    have hcost : (1 - t i) * (∑ j, c l j * L j) + t i * (∑ j, c r j * L j) ≤ ∑ j, c b j * L j := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_le_sum
      intro j _
      rw [← mul_assoc, ← mul_assoc, ← add_mul]
      exact mul_le_mul_of_nonneg_right (hc j) (by positivity)
    have he : V b ≤ (1 - t i) * V l + t i * V r := by
      unfold V
      linarith only [H_chord A o _ _ _ (ht i) (ht' i) hl hr m L, hcost]
    rcases le_total (V l) (V r) with h | h
    · exact ⟨true, he.trans (by linarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr (ht' i))])⟩
    · exact ⟨false, he.trans (by linarith [mul_le_mul_of_nonneg_left h (ht i)])⟩
  have aux (s : Finset ι) : ∃ b : ι → Option Bool,
      (∀ i, b i = none ↔ i ∉ s) ∧ V (fun _ => none) ≤ V b := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => none, by simp, le_rfl⟩
    | insert i s hi ih =>
      obtain ⟨b, hb, h⟩ := ih
      obtain ⟨a, ha⟩ := step b i ((hb i).mpr hi)
      refine ⟨_, fun j => ?_, h.trans ha⟩
      by_cases he : j = i <;> simp [he, hb]
  obtain ⟨b, hb, h⟩ := aux univ
  have he : ∀ i, ∃ a, b i = some a := by
    intro i
    have : b i ≠ none := by simp [hb]
    cases h' : b i <;> simp_all
  choose a ha using he
  refine ⟨a, ?_⟩
  have hba : b = fun i => some (a i) := funext ha
  rw [hba] at h
  exact h

/-- Every budget for the mixed placement is dominated, after costs, by
some budget at the outer placement. -/
theorem contract [Nonempty ι] (x y : ι → X) (f g t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1)
    (h₁ : ∀ i, Dist.dist o (y i) = t i * Dist.dist o (x i))
    (h₂ : ∀ i, Dist.dist (y i) (x i) = (1 - t i) * Dist.dist o (x i))
    (hg : ∀ i, t i * f i ≤ g i) (m : ℕ) (L : ι ⊕ ι → ℕ) :
    ∃ R, H A o (Sum.elim x y) m L - ∑ i, Sum.elim f g i * L i ≤ H A o x m R - ∑ i, f i * R i := by
  let a : ι ⊕ ι → ι := Sum.elim id id
  obtain ⟨b, hb⟩ := round_sites A o (x ∘ a) (Sum.elim x y) (f ∘ a) (Sum.elim f g)
    (Sum.elim (fun _ => 1) t) (by rintro (i|i) <;> simp [ht]) (by rintro (i|i) <;> simp [ht'])
    (by rintro (i|i) <;> simp [a, h₁]) (by rintro (i|i) <;> simp [a, h₂])
    (by rintro (i|i) <;> simp [a, hg]) m L
  let r i := if b i then some (a i) else none
  have he : (fun i => if b i then (x ∘ a) i else o) = fun i => (r i).elim o x := by
    funext i
    simp only [r]
    split <;> rfl
  have he' i : (if b i then (f ∘ a) i else 0) = (r i).elim 0 f := by
    simp only [r]
    split <;> rfl
  refine ⟨merged L r, hb.trans ?_⟩
  simp only [he, he', merged_cost]
  exact sub_le_sub_right (merge_price A o x m L r) _

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end
