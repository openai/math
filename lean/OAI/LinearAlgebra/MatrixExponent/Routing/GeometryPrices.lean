import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.Algebra.Group.Subgroup.Pointwise
import OAI.LinearAlgebra.MatrixExponent.Prices.Finite

section
/-!
# Local tensor price test

The tuple is allowed to repeat sites. Placement groups the
corresponding legs and gives unused sites trivial legs.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral

def Passes {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [DecidableEq I]
    (A : Finset (Tensor K S)) (B : Finset I) (c : I → I → Prop)
    (i j : I) (v : ℝ) (x : (S → I) → Tensor K S → ℝ) (ρ : ℝ)
    (P : Tensor K B → ℝ) : Prop :=
  (∀ a b : B, a.val = i → b.val = j → |v - P (Tensor.wire K a b 2)| ≤ ρ) ∧
  (∀ a b : B, c a.val b.val → P (Tensor.wire K a b 2) ≤ 1 + ρ) ∧
  ∀ z : S → B, ∀ u ∈ A, |x (Subtype.val ∘ z) u - P (Tensor.place z u)| ≤ ρ

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Finitely many constraints detect large displacement

Compactness is used on the table of squared distances itself. A
counterexample satisfying every constraint gives a complete geometric
action by metric completion. This avoids choosing an ultrafilter on
permutation inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Classical
open Set

variable {G : Type}

private abbrev Distances (G : Type) := Term G → Term G → ℝ

private theorem closed_table : IsClosed {R : Distances G | Table R} := by
  simp only [Table, ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun _ => isClosed_iInter fun _ => ?_).inter
    ((isClosed_iInter fun _ => ?_).inter
      ((isClosed_iInter fun _ => isClosed_iInter fun _ => ?_).inter
        ((isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_).inter
          (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
            isClosed_iInter fun _ => ?_))))
  all_goals first | exact isClosed_le (by fun_prop) (by fun_prop)
                  | exact isClosed_eq (by fun_prop) (by fun_prop)

private theorem closed_tests {E A B : Type} [Fintype E] [Fintype A] (p : E → A) (l : E → B) :
    IsClosed {R : Distances G | Tests R Term.seg p l} := by
  simp only [Tests, ofPred_forall]
  refine isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  simp only [joint, Fintype.expect_eq_sum_div_card]
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- Extract a uniform tolerance and a finite menu of continuous tests. -/
private theorem compact_tests {X I : Type} [TopologicalSpace X] {S : Set X}
    (hs : IsCompact S) (f : I → X → ℝ) (hc : ∀ i, Continuous (f i))
    (hf : ∀ x ∈ S, ∃ i, 0 < f i x) :
    ∃ t : Finset I, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∃ i ∈ t, δ < f i x := by
  let U (a : I × {t : ℝ // 0 < t}) := {x | a.2.val < f a.1 x}
  have ho (a) : IsOpen (U a) := isOpen_lt continuous_const (hc _)
  have hu : S ⊆ ⋃ a, U a := by
    intro x hx
    obtain ⟨i, hi⟩ := hf x hx
    exact mem_iUnion.mpr ⟨(i, ⟨f i x / 2, half_pos hi⟩), half_lt_self hi⟩
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover U ho hu
  let s := insert 1 (t.image fun a => a.2.val)
  have hn : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨t.image Prod.fst, s.min' hn, ?_, ?_⟩
  · have h := s.min'_mem hn
    rcases Finset.mem_insert.mp h with he | he
    · rw [he]; exact zero_lt_one
    · obtain ⟨a, _, he⟩ := Finset.mem_image.mp he
      exact he ▸ a.2.property
  · intro x hx
    obtain ⟨a, ha, he⟩ := mem_iUnion₂.mp (ht hx)
    have hm : a.2.val ∈ s := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
    exact ⟨_, Finset.mem_image_of_mem _ ha, (s.min'_le _ hm).trans_lt he⟩

variable [Group G] {E A B E' A' B' : Type} [Fintype E] [Fintype A]
  [Fintype E'] [Fintype A']

/-- Uniform displacement for complete actions satisfying two incidence estimates. -/
def Rigid (K : Set G) (p : E → A) (l : E → B) (p' : E' → A') (l' : E' → B') : Prop :=
  ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y] [MulAction G Y] [IsIsometricSMul G Y],
    Comparison Y → Incidence Y p l → Incidence Y p' l' →
    ∀ x : Y, (∀ g ∈ K, dist x (g • x) ≤ 1) → ∀ g : G, dist x (g • x) ≤ 1200

/-- A local hop constraint or a test of translation invariance. -/
abbrev Constraint (K : Set G) := K ⊕ (G × Term G × Term G)

def defect {K : Set G} (i : Constraint K) (R : Term G → Term G → ℝ) : ℝ :=
  match i with
  | .inl g => R (.mark 1) (.mark g.val) - 1
  | .inr (g, a, b) => |R (g • a) (g • b) - R a b|

variable [Nonempty E] [Nonempty A] [Nonempty E'] [Nonempty A']
  {K : Set G} {p : E → A} {l : E → B} {p' : E' → A'} {l' : E' → B'}

private theorem Rigid.exact (h : Rigid K p l p' l') {R : Distances G}
    (hr : Table R) (h₁ : Tests R Term.seg p l) (h₂ : Tests R Term.seg p' l')
    (hc : ∀ i : Constraint K, defect i R ≤ 0) (π : G) :
    R (.mark 1) (.mark π) ≤ 1200 ^ 2 := by
  have hg (g : G) (a b : Term G) : R (g • a) (g • b) = R a b :=
    sub_eq_zero.mp (abs_nonpos_iff.mp (hc (.inr (g, a, b))))
  obtain ⟨Y, _, _, _, _, C, f, hd, hs, he, hf⟩ := hr.realize hg
  let x := f (.mark 1)
  have hx (g : G) : dist x (g • x) ^ 2 = R (.mark 1) (.mark g) := by
    have heq : g • x = f (.mark g) := by
      rw [show x = f (.mark 1) from rfl, ← hf]
      change f (.mark (g * 1)) = _
      rw [mul_one]
    rw [heq]
    exact he _ _
  have hb : ∀ g ∈ K, dist x (g • x) ≤ 1 := by
    intro g hg
    have hh := hc (.inl ⟨g, hg⟩)
    change R (.mark 1) (.mark g) - 1 ≤ 0 at hh
    rw [← hx] at hh
    nlinarith
  rw [← hx]
  exact pow_le_pow_left₀ dist_nonneg
    (h Y C (h₁.dense C f hd hs he).incidence (h₂.dense C f hd hs he).incidence x hb π) 2

theorem Rigid.detect (h : Rigid K p l p' l') (π : G) (bound : Term G → Term G → ℝ) :
    ∃ t : Finset (Constraint K), ∃ δ : ℝ, 0 < δ ∧
    ∀ R : Term G → Term G → ℝ, R ≤ bound → Table R →
      Tests R Term.seg p l → Tests R Term.seg p' l' →
      (∀ i ∈ t, defect i R ≤ δ) → R (.mark 1) (.mark π) < 1200 ^ 2 + 1 := by
  let S := Icc 0 bound ∩ {R | Table R} ∩ {R | Tests R Term.seg p l} ∩
    {R | Tests R Term.seg p' l'} ∩ {R | 1200 ^ 2 + 1 ≤ R (.mark 1) (.mark π)}
  have hs : IsCompact S :=
    ((((isCompact_Icc.inter_right closed_table).inter_right (closed_tests p l)).inter_right
      (closed_tests p' l')).inter_right (isClosed_le (by fun_prop) (by fun_prop)))
  have hc (i : Constraint K) : Continuous (defect i) := by
    rcases i with g | ⟨g, a, b⟩ <;> unfold defect <;> fun_prop
  obtain ⟨t, δ, hδ, ht⟩ := compact_tests hs defect hc (by
    rintro R ⟨⟨⟨⟨_, hr⟩, h₁⟩, h₂⟩, bad⟩
    by_contra! hh
    exact (not_le_of_gt (lt_add_one _)) (bad.trans (h.exact hr h₁ h₂ hh π)))
  refine ⟨t, δ, hδ, ?_⟩
  intro R hb hr h₁ h₂ hd
  by_contra! bad
  obtain ⟨i, hi, he⟩ := ht R ⟨⟨⟨⟨⟨hr.1, hb⟩, hr⟩, h₁⟩, h₂⟩, bad⟩
  exact he.not_ge (hd i hi)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Averaging finite placements

Tables of squared distances average linearly. The pseudometric triangle
inequality for the square root follows by Cauchy-Schwarz.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators
variable {G I E A B : Type}

structure Placement (G : Type) where
  Site : Type
  [space : MetricSpace Site]
  [complete : CompleteSpace Site]
  cmp : Comparison Site
  mark : G → Site

attribute [instance] Placement.space Placement.complete

namespace Placement

def eval (X : Placement G) : Term G → X.Site := Term.eval X.cmp X.mark

def sq (X : Placement G) (u v : Term G) := dsq (X.eval u) (X.eval v)

variable [Fintype I]

def average (Z : I → Placement G) (u v : Term G) := 𝔼 i, (Z i).sq u v

private theorem rms_triangle (a b c : I → ℝ) (h₀ : ∀ i, 0 ≤ c i)
    (h : ∀ i, c i ≤ a i + b i) :
    Real.sqrt (𝔼 i, c i ^ 2) ≤ Real.sqrt (𝔼 i, a i ^ 2) + Real.sqrt (𝔼 i, b i ^ 2) := by
  let x := 𝔼 i, a i ^ 2
  let y := 𝔼 i, b i ^ 2
  have hx : 0 ≤ x := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hy : 0 ≤ y := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hxy : (𝔼 i, a i * b i) ≤ Real.sqrt x * Real.sqrt y := by
    rw [← Real.sqrt_mul hx]
    exact Real.le_sqrt_of_sq_le (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ a b)
  have hh (i : I) : c i ^ 2 ≤ a i ^ 2 + b i ^ 2 + 2 * (a i * b i) := by
    linarith only [pow_le_pow_left₀ (h₀ i) (h i) 2]
  have he := Finset.expect_le_expect (s := Finset.univ) fun i _ => hh i
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at he
  change Real.sqrt _ ≤ Real.sqrt x + Real.sqrt y
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  change _ ≤ x + y + 2 * (𝔼 i, a i * b i) at he
  linarith only [he, hxy, Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem table (Z : I → Placement G) : Table (average Z) := by
  refine ⟨fun _ _ => Finset.expect_nonneg (fun _ _ => sq_nonneg _), ?_, ?_, ?_, ?_⟩
  · intro x
    simp [average, sq, dsq]
  · intro x y
    simp only [average, sq, dsq, dist_comm]
  · intro x y z
    exact rms_triangle _ _ _ (fun _ => dist_nonneg) (fun _ => dist_triangle _ _ _)
  · intro t x y z
    have h (i : I) : (Z i).sq (.seg t x y) z ≤
        (1 - t.val) * (Z i).sq x z + t.val * (Z i).sq y z - t.val * (1 - t.val) * (Z i).sq x y :=
      (Z i).cmp.along t _ _ _
    have he := Finset.expect_le_expect (s := Finset.univ) (fun i _ => h i)
    simpa only [average, Finset.expect_sub_distrib, Finset.expect_add_distrib,
      ← Finset.mul_expect] using he

variable [Fintype E] [Nonempty E] [Fintype A] [Nonempty A] {p : E → A} {l : E → B}

private theorem tests (X : Placement G) (h : Incidence X.Site p l) : Tests X.sq Term.seg p l := by
  intro x y b n t ht
  have hs (u : Fin (n + 1) → A) :
      X.eval (sampleMean Term.seg n (x ∘ u)) = sampleMean X.cmp.seg n ((X.eval ∘ x) ∘ u) :=
    sampleMean_map Term.seg X.cmp.seg X.eval (fun _ _ _ => rfl) n _
  simp only [joint, sq, hs, Function.comp_apply]
  exact h.tests X.cmp (X.eval ∘ x) (X.eval ∘ y) (X.eval b) n t ht

theorem average_tests (Z : I → Placement G) (h : ∀ i, Incidence (Z i).Site p l) :
    Tests (average Z) Term.seg p l := by
  intro x y b n t ht
  have he := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => (Z i).tests (h i) x y b n t ht)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at he
  have hj (u : Term G) :
      joint (average Z) (x ∘ p) (y ∘ l) u = 𝔼 i, joint (Z i).sq (x ∘ p) (y ∘ l) u := by
    unfold joint average
    simp only [← Finset.expect_add_distrib]
    exact Finset.expect_comm _ _ _
  simp only [hj, average]
  rw [Finset.expect_comm (Finset.univ : Finset (Fin (n + 1) → A)),
    Finset.expect_comm (Finset.univ : Finset E), Finset.expect_comm (Finset.univ : Finset A)]
  exact he

end Placement
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Finite detection on almost all centers

Each center may have a different metric space. Comparisons are made
after reindexing centers by a permutation, off a small exceptional set.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Classical
variable {G I : Type} [Group G] [Fintype I] [Nonempty I]

omit [Nonempty I] in
private theorem expect_perm (π : Equiv.Perm I) (f : I → ℝ) :
    (𝔼 i, f (π i)) = 𝔼 i, f i :=
  Fintype.expect_equiv π _ _ (fun _ => rfl)

/-- Probability of falling outside a set of good centers. -/
def badFraction (good : Set I) := 𝔼 i, if i ∈ good then 0 else (1 : ℝ)

private theorem expect_good (good : Set I) (π : Equiv.Perm I) (f : I → ℝ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hb : badFraction good ≤ δ)
    (hall : ∀ i, f i ≤ M) (hgood : ∀ i ∈ good, π i ∈ good → f i ≤ δ) :
    (𝔼 i, f i) ≤ (1 + 2 * M) * δ := by
  let b := fun i => if i ∈ good then 0 else (1 : ℝ)
  have h (i : I) : f i ≤ δ + M * (b i + b (π i)) := by
    by_cases hi : i ∈ good
    · by_cases hj : π i ∈ good
      · simpa [b, hi, hj] using hgood i hi hj
      · simp only [b, ite_eq_left hi, ite_eq_right hj]
        linarith [hall i]
    · have hn : 0 ≤ b (π i) := by unfold b; split <;> norm_num
      rw [show b i = 1 from ite_eq_right hi]
      linarith [hall i, mul_nonneg hM hn]
  have he := Finset.expect_le_expect (s := Finset.univ) fun i _ => h i
  rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
    Finset.expect_add_distrib, expect_perm] at he
  change (𝔼 i, b i) ≤ δ at hb
  linarith only [he, mul_le_mul_of_nonneg_left hb hM]

variable {K : Set G}

def Constraint.shift (π : G → Equiv.Perm I) : Constraint K → Equiv.Perm I
  | .inl _ => Equiv.refl _
  | .inr (g, _, _) => π g

def Constraint.error (Z : I → Placement G) (π : G → Equiv.Perm I) (i : I) :
    Constraint K → ℝ
  | .inl g => (Z i).sq (.mark 1) (.mark g.val) - 1
  | .inr (g, x, y) => |(Z i).sq (g • x) (g • y) - (Z (π g i)).sq x y|

private theorem average_defect (Z : I → Placement G) (π : G → Equiv.Perm I) (c : Constraint K) :
    defect c (Placement.average Z) ≤ (𝔼 i, Constraint.error Z π i c) := by
  rcases c with g | ⟨g, x, y⟩
  · simp only [defect, Placement.average, Constraint.error,
      Finset.expect_sub_distrib, Fintype.expect_const, le_refl]
  · simp only [defect, Placement.average, Constraint.error]
    rw [← expect_perm (π g) (fun i => (Z i).sq x y), ← Finset.expect_sub_distrib]
    apply abs_le.mpr
    constructor
    · rw [← Finset.expect_neg_distrib]
      exact Finset.expect_le_expect (fun _ _ => neg_abs_le _)
    · exact Finset.expect_le_expect (fun _ _ => le_abs_self _)

private def cap (bound : Term G → Term G → ℝ) : Constraint K → ℝ
  | .inl g => bound (.mark 1) (.mark g.val)
  | .inr (g, x, y) => bound (g • x) (g • y) + bound x y

omit [Fintype I] [Nonempty I] in
private theorem error_le_cap (Z : I → Placement G) (π : G → Equiv.Perm I)
    (bound : Term G → Term G → ℝ) (h : ∀ i, (Z i).sq ≤ bound)
    (i : I) (c : Constraint K) : Constraint.error Z π i c ≤ cap bound c := by
  rcases c with g | ⟨g, x, y⟩
  · exact (sub_le_self _ zero_le_one).trans (h i _ _)
  · have h₁ : 0 ≤ (Z i).sq (g • x) (g • y) := sq_nonneg _
    have h₂ : 0 ≤ (Z (π g i)).sq x y := sq_nonneg _
    apply abs_le.mpr
    dsimp only [cap]
    constructor <;> linarith [h i (g • x) (g • y), h (π g i) x y]

variable {E A B E' A' B' : Type} [Fintype E] [Fintype A] [Fintype E'] [Fintype A']
  [Nonempty E] [Nonempty A] [Nonempty E'] [Nonempty A']
  {p : E → A} {l : E → B} {p' : E' → A'} {l' : E' → B'}

/-- The finite metric tests, payload tolerance and exceptional fraction
are independent of the number of centers. -/
theorem Rigid.detect_local (h : Rigid K p l p' l') (g : G)
    (bound : Term G → Term G → ℝ) (pay : ℝ) :
    ∃ t : Finset (Constraint K), ∃ δ : ℝ, 0 < δ ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (Z : I → Placement G)
      (π : G → Equiv.Perm I) (good : Set I) (v : I → ℝ),
      (∀ i, Incidence (Z i).Site p l) → (∀ i, Incidence (Z i).Site p' l') →
      (∀ i, (Z i).sq ≤ bound) → (∀ i, v i ^ 2 ≤ pay) → badFraction good ≤ δ →
      (∀ c ∈ t, ∀ i ∈ good, Constraint.shift π c i ∈ good → Constraint.error Z π i c ≤ δ) →
      (∀ i ∈ good, v i ^ 2 ≤ (Z i).sq (.mark 1) (.mark g) + δ) →
      (𝔼 i, v i) ≤ 1201 := by
  obtain ⟨t, ε, hε, ht⟩ := h.detect g bound
  let M := |pay| + ∑ c ∈ t, |cap bound c|
  have hM : 0 ≤ M := by unfold M; positivity
  have hm (c) (hc : c ∈ t) : cap bound c ≤ M :=
    (le_abs_self _).trans ((Finset.single_le_sum (fun c _ => abs_nonneg (cap bound c)) hc).trans
      (le_add_of_nonneg_left (abs_nonneg _)))
  have hp : pay ≤ M := (le_abs_self _).trans (le_add_of_nonneg_right (by positivity))
  let δ := min 1 ε / (1 + 2 * M)
  have hδ : 0 < δ := div_pos (lt_min zero_lt_one hε) (by positivity)
  have hd : (1 + 2 * M) * δ = min 1 ε := mul_div_cancel₀ _ (by positivity)
  refine ⟨t, δ, hδ, ?_⟩
  intro I _ _ Z π good v h₁ h₂ hb hv hg hc hv'
  have havg : Placement.average Z ≤ bound := fun x y =>
    Finset.expect_le Finset.univ_nonempty (fun i _ => hb i x y)
  have hctrl (c) (hc' : c ∈ t) : defect c (Placement.average Z) ≤ ε := by
    refine (average_defect Z π c).trans ((expect_good good (Constraint.shift π c) _
      hM hδ.le hg ?_ (hc c hc')).trans (hd.le.trans (min_le_right _ _)))
    intro i
    exact (error_le_cap Z π bound hb i c).trans (hm c hc')
  have H := ht _ havg (Placement.table Z) (Placement.average_tests Z h₁)
    (Placement.average_tests Z h₂) hctrl
  have L := expect_good good (Equiv.refl I)
    (fun i => v i ^ 2 - (Z i).sq (.mark 1) (.mark g)) hM hδ.le hg
    (fun i => (sub_le_self _ (sq_nonneg _)).trans ((hv i).trans hp))
    (fun i hi _ => sub_le_iff_le_add'.mpr (hv' i hi))
  rw [Finset.expect_sub_distrib, hd] at L
  have hs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ v (fun _ => (1 : ℝ))
  simp only [one_pow, Fintype.expect_const, mul_one] at hs
  unfold Placement.average at H
  nlinarith [min_le_left (1 : ℝ) ε]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Restricting detection to finitely many marked sites

We discard marks outside their prescribed distance bounds. All
expressions needed by the finite tests use only marks in a single
finite set and its translates.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Classical
variable {G F : Type} {Y : Type*} [MetricSpace Y]

namespace Term

def support : Term G → Finset G
  | .mark g => {g}
  | .seg _ a b => support a ∪ support b

theorem eval_map (C : Comparison Y) (x : F → Y) (f : G → F) (a : Term G) :
    eval C x (map f a) = eval C (x ∘ f) a := by
  induction a <;> simp [eval, map, *]

theorem eval_congr (C : Comparison Y) (x y : G → Y) (a : Term G)
    (h : ∀ g ∈ a.support, x g = y g) : eval C x a = eval C y a := by
  induction a with
  | mark g => exact h g (Finset.mem_singleton_self _)
  | seg u a b ha hb =>
    exact congrArg₂ (C.seg u) (ha (fun g hg => h g (Finset.mem_union_left _ hg)))
      (hb (fun g hg => h g (Finset.mem_union_right _ hg)))

private def height (L : G → ℝ) : Term G → ℝ
  | .mark g => L g ^ 2
  | .seg t a b => (1 - t.val) * height L a + t.val * height L b

private theorem eval_bound (C : Comparison Y) (x : G → Y) (o : Y) (L : G → ℝ)
    (h : ∀ g, dist (x g) o ^ 2 ≤ L g ^ 2) (a : Term G) :
    dist (eval C x a) o ^ 2 ≤ height L a := by
  induction a with
  | mark => exact h _
  | seg t a b ha hb =>
    have h₁ := t.2.1
    have h₂ := sub_nonneg.mpr t.2.2
    exact ((C.along _ _ _ _).trans (sub_le_self _ (by positivity))).trans
      (add_le_add (mul_le_mul_of_nonneg_left ha h₂) (mul_le_mul_of_nonneg_left hb h₁))

end Term

variable [Group G] {K : Set G}

private def truncate (L : G → ℝ) (X : Placement G) (g : G) : X.Site :=
  if dist (X.mark g) (X.mark 1) ^ 2 ≤ L g ^ 2 then X.mark g else X.mark 1

private def bounded (L : G → ℝ) (X : Placement G) : Placement G :=
  { X with mark := truncate L X }

private theorem bounded_sq (L : G → ℝ) (X : Placement G) (a b : Term G) :
    (bounded L X).sq a b ≤ 2 * Term.height L a + 2 * Term.height L b := by
  have h (g : G) : dist (truncate L X g) (X.mark 1) ^ 2 ≤ L g ^ 2 := by
    unfold truncate
    split
    · assumption
    · simpa using sq_nonneg (L g)
  let f := Term.eval X.cmp (truncate L X)
  change dist (f a) (f b) ^ 2 ≤ _
  have ht := dist_sq_triangle (f a) (X.mark 1) (f b)
  rw [dist_comm (X.mark 1)] at ht
  dsimp only [f] at ht ⊢
  linarith only [ht, Term.eval_bound X.cmp _ _ _ h a, Term.eval_bound X.cmp _ _ _ h b]

private def words : Constraint K → Finset (Term G)
  | .inl g => {.mark g.val}
  | .inr (g, a, b) => {.mark g, a, b}

private def retract (S : Finset G) (hS : 1 ∈ S) (g : G) : S :=
  if h : g ∈ S then ⟨g, h⟩ else ⟨1, hS⟩

/-- Squared distance in a translated finite marking. -/
def Placement.on (X : Placement G) (S : Finset G) (g : G) (a b : Term S) :=
  let f := Term.eval X.cmp (fun j : S => X.mark (g * j.val))
  dsq (f a) (f b)

private theorem bounded_on (L : G → ℝ) (X : Placement G) (S : Finset G) (hS : 1 ∈ S)
    (g : G) (hg : ∀ j ∈ S, dist (X.mark (g * j)) (X.mark 1) ^ 2 ≤ L (g * j) ^ 2)
    (a b : Term G) (ha : a.support ⊆ S) (hb : b.support ⊆ S) :
    (bounded L X).sq (g • a) (g • b) =
      X.on S g (a.map (retract S hS)) (b.map (retract S hS)) := by
  have eq (w : Term G) (hw : w.support ⊆ S) :
      Term.eval X.cmp (truncate L X) (g • w) =
        Term.eval X.cmp (fun j : S => X.mark (g * j.val)) (w.map (retract S hS)) := by
    change Term.eval _ _ (Term.map _ w) = _
    rw [Term.eval_map, Term.eval_map]
    apply Term.eval_congr
    intro i hi
    simp only [Function.comp_apply, retract, dite_eq_left (hw hi), truncate, ite_eq_left (hg i (hw hi))]
  exact congrArg₂ dsq (eq a ha) (eq b hb)

variable {E A B E' A' B' : Type} [Fintype E] [Fintype A] [Fintype E'] [Fintype A']
  [Nonempty E] [Nonempty A] [Nonempty E'] [Nonempty A']
  {p : E → A} {l : E → B} {p' : E' → A'} {l' : E' → B'}

theorem Rigid.detect_sites (h : Rigid K p l p' l') (g : G) (L : G → ℝ) (pay : ℝ) :
    ∃ S : Finset G, 1 ∈ S ∧ g ∈ S ∧ ∃ U : Finset (Term S), ∃ δ : ℝ, 0 < δ ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (Z : I → Placement G)
      (π : G → Equiv.Perm I) (good : Set I) (v : I → ℝ),
      (∀ i, Incidence (Z i).Site p l) → (∀ i, Incidence (Z i).Site p' l') →
      (∀ i, v i ^ 2 ≤ pay) → badFraction good ≤ δ →
      (∀ i ∈ good, ∀ a ∈ S, ∀ b ∈ S, dist ((Z i).mark (a * b)) ((Z i).mark 1) ^ 2 ≤ L (a * b) ^ 2) →
      (∀ i ∈ good, ∀ a ∈ S, a ∈ K → dist ((Z i).mark 1) ((Z i).mark a) ^ 2 ≤ 1 + δ) →
      (∀ i ∈ good, ∀ a ∈ S, π a i ∈ good → ∀ u ∈ U, ∀ w ∈ U,
        |(Z i).on S a u w - (Z (π a i)).on S 1 u w| ≤ δ) →
      (∀ i ∈ good, v i ^ 2 ≤ dist ((Z i).mark 1) ((Z i).mark g) ^ 2 + δ) →
      (𝔼 i, v i) ≤ 1201 := by
  obtain ⟨t, δ, hδ, ht⟩ := h.detect_local g (fun u v => 2 * Term.height L u + 2 * Term.height L v) pay
  let F := t.biUnion words
  let S := insert 1 (insert g (F.biUnion Term.support))
  have hS : 1 ∈ S := by simp [S]
  have hg : g ∈ S := by simp [S]
  have hs {u : Term G} (hu : u ∈ F) : u.support ⊆ S := by
    intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hx⟩))
  have hm {a : G} (ha : Term.mark a ∈ F) : a ∈ S := hs ha (Finset.mem_singleton_self _)
  let U := F.image (Term.map (retract S hS))
  refine ⟨S, hS, hg, U, δ, hδ, ?_⟩
  intro I _ _ Z π good v h₁ h₂ hv hgood hb hhop hterm hpay
  have he (i : I) (hi : i ∈ good) (a : G) (ha : a ∈ S) :
      (bounded L (Z i)).sq (.mark 1) (.mark a) =
        dist ((Z i).mark 1) ((Z i).mark a) ^ 2 := by
    have h' (j : G) (hj : j ∈ S) : truncate L (Z i) j = (Z i).mark j := by
      apply ite_eq_left
      simpa using hb i hi 1 hS j hj
    change dist (truncate L (Z i) 1) (truncate L (Z i) a) ^ 2 = _
    rw [h' 1 hS, h' a ha]
  refine ht I (fun i => bounded L (Z i)) π good v h₁ h₂
    (fun i a b => bounded_sq L (Z i) a b) hv hgood ?_ ?_
  · intro c hc i hi hi'
    have hc' : words c ⊆ F := fun _ hu => Finset.mem_biUnion.mpr ⟨c, hc, hu⟩
    rcases c with a | ⟨a, u, w⟩
    · have ha : a.val ∈ S := hm (hc' (by simp [words]))
      simp only [Constraint.error, he i hi a.val ha]
      linarith [hhop i hi a.val ha a.property]
    · have ha : a ∈ S := hm (hc' (by simp [words]))
      have hu : u ∈ F := hc' (by simp [words])
      have hw : w ∈ F := hc' (by simp [words])
      have hk := bounded_on L (Z (π a i)) S hS 1 (hb _ hi' 1 hS) u w (hs hu) (hs hw)
      simp only [one_smul] at hk
      rw [Constraint.error, bounded_on L (Z i) S hS a (hb _ hi a ha) u w (hs hu) (hs hw), hk]
      exact hterm i hi a ha hi' _ (Finset.mem_image_of_mem _ hu) _ (Finset.mem_image_of_mem _ hw)
  · intro i hi
    rw [he i hi g hg]
    exact hpay i hi

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Finite balls of hops

A fixed factorization length is assigned to each element of a group
generated by subgroups. For any finite list of elements, finitely many
hops suffice to realize all those lengths in every permutation action.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped Classical Pointwise
variable {G P I : Type} [Group G]

def hops (K : P → Subgroup G) : Set G := ⋃ p, (K p : Set G)

private theorem factor (K : P → Subgroup G) (hg : iSup K = ⊤) (g : G) :
    ∃ (n : ℕ) (s : Finset G), (↑s : Set G) ⊆ hops K ∧ g ∈ s ^ n := by
  have h : g ∈ iSup K := by rw [hg]; trivial
  refine Subgroup.iSup_induction K (C := fun g => ∃ (n : ℕ) (s : Finset G),
    (↑s : Set G) ⊆ hops K ∧ g ∈ s ^ n) h ?_ ?_ ?_
  · intro p x hx
    refine ⟨1, {x}, ?_, by simp⟩
    simpa only [Finset.coe_singleton, Set.singleton_subset_iff, hops, Set.mem_iUnion] using
      (show ∃ p, x ∈ (K p : Set G) from ⟨p, hx⟩)
  · exact ⟨0, ∅, by simp, by simp⟩
  · intro x y hx hy
    obtain ⟨n, s, hs, hx⟩ := hx
    obtain ⟨m, t, ht, hy⟩ := hy
    refine ⟨n + m, s ∪ t, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hs ht
    · rw [pow_add]
      exact Finset.mul_mem_mul (Finset.pow_subset_pow_left Finset.subset_union_left hx)
        (Finset.pow_subset_pow_left Finset.subset_union_right hy)

theorem finite_hops [Nonempty P] (K : P → Subgroup G) (hg : iSup K = ⊤) :
    ∃ len : G → ℕ, ∀ S : Finset G, ∃ (H : Finset G) (r : ℕ),
      1 ∈ H ∧ H⁻¹ = H ∧ (↑H : Set G) ⊆ hops K ∧
      (∀ g ∈ S, g ∈ hops K → g ∈ H) ∧ (∀ g ∈ S, g ∈ H ^ (len g) ∧ len g ≤ r) := by
  choose len t ht he using factor K hg
  refine ⟨len, ?_⟩
  intro S
  let F := insert 1 ((S.filter (· ∈ hops K)) ∪ S.biUnion t)
  let H := F ∪ F⁻¹
  have hF : (↑F : Set G) ⊆ hops K := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Set.mem_iUnion.mpr ⟨Classical.arbitrary P, Subgroup.one_mem _⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
      exact ht k hk
  refine ⟨H, S.sup len, by simp [H, F], ?_, ?_, ?_, ?_⟩
  · ext
    simp [H, or_comm]
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hF hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_inv.mp hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hF hy)
    exact Set.mem_iUnion.mpr ⟨p, (K p).inv_mem hp⟩
  · intro g hs hh
    simp [H, F, hs, hh]
  · intro g hs
    refine ⟨Finset.pow_subset_pow_left ?_ (he g), Finset.le_sup hs⟩
    intro a ha
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, hs, ha⟩)))

variable [MulAction G I]

def ball (H : Finset G) (r : ℕ) (i : I) : Finset I := (H ^ r).image (fun a => a⁻¹ • i)

def link (H : Finset G) (i j : I) : Prop := ∃ a ∈ H, a⁻¹ • i = j

theorem mem_ball {H : Finset G} {r : ℕ} (i : I) {a : G} (ha : a ∈ H ^ r) :
    a⁻¹ • i ∈ ball H r i := Finset.mem_image_of_mem _ ha

/-- A path of the prescribed length stays inside the ball. -/
theorem ball_path {H : Finset G} (hH : 1 ∈ H) {r : ℕ} (i : I)
    {Q : I → ℕ → Prop} (h₀ : Q i 0)
    (hs : ∀ j ∈ ball H r i, ∀ k ∈ ball H r i, ∀ n, link H j k → Q j n → Q k (n + 1))
    {n : ℕ} (hn : n ≤ r) {a : G} (ha : a ∈ H ^ n) : Q (a⁻¹ • i) n := by
  induction n generalizing a with
  | zero =>
    have : a = 1 := Finset.mem_one.mp (by simpa using ha)
    simpa [this]
  | succ n ih =>
    have hm := mem_ball i (Finset.pow_subset_pow_right hH hn ha)
    rw [pow_succ, Finset.mem_mul] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    have hnr : n ≤ r := by omega
    exact hs _ (mem_ball i (Finset.pow_subset_pow_right hH hnr hb)) _ hm n
      ⟨c, hc, by rw [mul_inv_rev, mul_smul]⟩ (ih hnr hb)

theorem ball_dist {Y : Type*} [MetricSpace Y] {H : Finset G} (hH : 1 ∈ H)
    {r : ℕ} {i : I} (x : I → Y) (hs : ∀ j ∈ ball H r i, ∀ k ∈ ball H r i,
      link H j k → dist (x j) (x k) ≤ 2)
    {n : ℕ} (hn : n ≤ r) {a : G} (ha : a ∈ H ^ n) :
    dist (x (a⁻¹ • i)) (x i) ≤ 2 * n := by
  refine ball_path hH i (Q := fun j n => dist (x j) (x i) ≤ 2 * n) (by simp) ?_ hn ha
  intro j hj k hk m he hd
  have ht := dist_triangle (x k) (x j) (x i)
  rw [dist_comm (x k) (x j)] at ht
  push_cast
  linarith [hs j hj k hk he]

theorem center_mem_ball {H : Finset G} (hH : 1 ∈ H) (r : ℕ) (i : I) : i ∈ ball H r i := by
  simpa using mem_ball i (Finset.one_mem_pow (n := r) hH)

theorem ball_connected {H : Finset G} (hH : 1 ∈ H) (r : ℕ) (i : I) (x y : ball H r i) :
    Relation.EqvGen (fun j k : ball H r i => link H j.val k.val) x y := by
  let c : ball H r i := ⟨i, center_mem_ball hH r i⟩
  let l := fun j k : ball H r i => link H j.val k.val
  have hc (z : ball H r i) : Relation.EqvGen l c z := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp z.property
    have h : ∀ hm : a⁻¹ • i ∈ ball H r i, Relation.EqvGen l c ⟨a⁻¹ • i, hm⟩ := by
      refine ball_path hH i (Q := fun j _ => ∀ hj, Relation.EqvGen l c ⟨j, hj⟩) ?_ ?_ le_rfl ha
      · exact fun _ => .refl _
      · exact fun _ hj _ hk _ he h _ => .trans _ _ _ (h hj) (.rel _ _ he)
    simpa only [he, Subtype.eta] using h (mem_ball i ha)
  exact .trans _ _ _ (.symm _ _ (hc x)) (hc y)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Finite detection of expensive payloads

Prices are shared by all balls containing a given tuple, including
tuples with coincidences. The certificate consists of symmetric hops,
a radius, a finite list of nonzero tensors and a positive tolerance.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped BigOperators Classical Pointwise

variable {k G J I E A B E' A' B' : Type} [Field k]
  [Fintype E] [Fintype A] [Fintype E'] [Fintype A']

/-- Realization of ordinary and collapsed prices with the two links. -/
def HasModels (k : Type) [Field k] (p : E → A) (l : E → B) (p' : E' → A') (l' : E' → B') : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (P : Tensor k S → ℝ),
    (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary k S D) → ∃ X : Placement S,
      Represents k P X.mark ∧ Incidence X.Site p l ∧ Incidence X.Site p' l'

variable {p : E → A} {l : E → B} {p' : E' → A'} {l' : E' → B'}

private theorem HasModels.extend (h : HasModels k p l p' l') (N : Finset I)
    (i : N) (P : Tensor k N → ℝ) (hp : P = 0 ∨ ∃ D, P ∈ Tensor.ordinary k N D) :
    ∃ X : Placement I, Represents k P (X.mark ∘ Subtype.val) ∧
      Incidence X.Site p l ∧ Incidence X.Site p' l' := by
  have : Nonempty N := ⟨i⟩
  obtain ⟨X, hx, h₁, h₂⟩ := h N P hp
  let y := fun j => if hj : j ∈ N then X.mark ⟨j, hj⟩ else X.mark i
  have hy : y ∘ Subtype.val = X.mark := by ext j; simp [y, j.property]
  refine ⟨⟨X.Site, X.cmp, y⟩, ?_, h₁, h₂⟩
  change Represents k P (y ∘ Subtype.val)
  rwa [hy]

private theorem price_zero {T : Type} [Fintype T] {P : Tensor k T → ℝ}
    (hp : P = 0 ∨ ∃ D, P ∈ Tensor.ordinary k T D) : P 0 = 0 := by
  rcases hp with rfl | ⟨_, _, _, _, _, rfl⟩ <;> simp [Tensor.values]

variable [Group G]

private def markOrbit [MulAction G I] (i : I) (X : Placement I) : Placement G :=
  ⟨X.Site, X.cmp, fun g => X.mark (g⁻¹ • i)⟩

/-- Both sampled marks and all intermediate hops on their paths lie in
the indicated ball. -/
private theorem orbit_estimates [MulAction G I] {H S : Finset G} (hH : 1 ∈ H)
    {len : G → ℕ} {r : ℕ} (hl : ∀ a ∈ S * S, a ∈ H ^ (len a) ∧ len a ≤ r)
    (i : I) (X : Placement I)
    (hd : ∀ j ∈ ball H r i, ∀ u ∈ ball H r i, link H j u → dist (X.mark j) (X.mark u) ≤ 2)
    (a : G) (ha : a ∈ S) (b : G) (hb : b ∈ S) :
    (a * b)⁻¹ • i ∈ ball H r i ∧
      dist (X.mark ((a * b)⁻¹ • i)) (X.mark i) ≤ 2 * len (a * b) := by
  obtain ⟨h₁, h₂⟩ := hl _ (Finset.mul_mem_mul ha hb)
  exact ⟨mem_ball i (Finset.pow_subset_pow_right hH h₂ h₁),
    ball_dist hH X.mark hd h₂ h₁⟩

variable [Nonempty E] [Nonempty A] [Nonempty E'] [Nonempty A'] [Nonempty J]

theorem Rigid.finite_detection (K : J → Subgroup G) (hgen : iSup K = ⊤)
    (h : Rigid (hops K) p l p' l') (hm : HasModels k p l p' l') (g : G) :
    ∃ S H : Finset G, ∃ d r : ℕ, ∃ T : Finset (Tensor k S), ∃ ρ : ℝ,
      1 ∈ S ∧ 1 ∈ H ∧ H⁻¹ = H ∧ (↑H : Set G) ⊆ hops K ∧ 0 < d ∧ d ≤ r ∧ g ∈ H ^ d ∧ 0 ∉ T ∧ 0 < ρ ∧
      ∀ (I : Type) [Fintype I] [Nonempty I] [MulAction G I] (v : I → ℝ)
        (x : (S → I) → Tensor k S → ℝ) (good : Set I),
        (∀ i, |v i| ≤ d) → badFraction good ≤ ρ →
        (∀ i ∈ good, ∃ P : Tensor k (ball H r i) → ℝ,
          (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary k (ball H r i) D) ∧
          Passes T (ball H r i) (link H) i (g⁻¹ • i) (v i) x ρ P) →
        (𝔼 i, v i) ≤ 1201 := by
  obtain ⟨len, hf⟩ := finite_hops K hgen
  let d := len g + 1
  obtain ⟨S, hS, hg, U, δ, hδ, hdet⟩ := h.detect_sites g (fun a => 2 * len a) ((d : ℝ) ^ 2)
  have : Nonempty S := ⟨⟨1, hS⟩⟩
  obtain ⟨H, r₀, hH, hinv, hK, hhop, hl₀⟩ := hf (S * S)
  let r := max r₀ d
  have hl (a : G) (ha : a ∈ S * S) : a ∈ H ^ (len a) ∧ len a ≤ r :=
    ⟨(hl₀ a ha).1, (hl₀ a ha).2.trans (le_max_left _ _)⟩
  have hsub (a : G) (ha : a ∈ S) : a ∈ S * S := by
    simpa using Finset.mul_mem_mul hS ha
  have hmem (a : G) (ha : a ∈ S * S) : a ∈ H ^ r :=
    Finset.pow_subset_pow_right hH (hl a ha).2 (hl a ha).1
  let D : ℝ := 4 * r + 1
  obtain ⟨T, η, hη, htest⟩ := finite_terms_tests k U D hδ
  let ρ := min (min 1 (η / 2)) (δ / (D + 3))
  have hD : 0 < D := by unfold D; positivity
  have hp : 0 < ρ := by unfold ρ; positivity
  have hρ : ρ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hη' : 2 * ρ ≤ η := by
    have hh : ρ ≤ η / 2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hd : ρ * (D + 3) ≤ δ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hroute : g ∈ H ^ d := Finset.pow_subset_pow_right hH (Nat.le_succ _) (hl g (hsub g hg)).1
  refine ⟨S, H, d, r, T.erase 0, ρ, hS, hH, hinv, hK, Nat.succ_pos _, le_max_right _ _, hroute,
    Finset.notMem_erase _ _, hp, ?_⟩
  intro I _ _ _ v x good hv hbad hpass
  let N : I → Finset I := ball H r
  have hc (i : I) : i ∈ N i := center_mem_ball hH r i
  have hmemb (i : I) (a : G) (ha : a ∈ S) : a⁻¹ • i ∈ N i := mem_ball i (hmem a (hsub a ha))
  have hall (i : I) : ∃ P : Tensor k (N i) → ℝ,
      (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary k (N i) D) ∧
      (i ∈ good → Passes (T.erase 0) (N i) (link H) i (g⁻¹ • i) (v i) x ρ P) := by
    by_cases hi : i ∈ good
    · obtain ⟨P, hP, he⟩ := hpass i hi
      exact ⟨P, hP, fun _ => he⟩
    · exact ⟨0, Or.inl rfl, fun hj => (hi hj).elim⟩
  choose P hP ht using hall
  choose X hX h₁ h₂ using fun i => hm.extend (N i) ⟨i, hc i⟩ (P i) (hP i)
  have hh (i : I) (hi : i ∈ good) (a : I) (ha : a ∈ N i) (b : I) (hb : b ∈ N i)
      (he : link H a b) : dist ((X i).mark a) ((X i).mark b) ≤ 1 + ρ := by
    have hh := (ht i hi).2.1 ⟨a, ha⟩ ⟨b, hb⟩ he
    rwa [(hX i).1] at hh
  have hdist (i : I) (hi : i ∈ good) (a : G) (ha : a ∈ S) (b : G) (hb : b ∈ S) :=
    orbit_estimates hH hl i (X i) (fun j hj u hu he => (hh i hi j hj u hu he).trans
      (show 1 + ρ ≤ 2 by linarith)) a ha b hb
  have hrad (i : I) (hi : i ∈ good) (a : G) (ha : a ∈ S) (b : G) (hb : b ∈ S) :
      dist ((X i).mark ((a * b)⁻¹ • i)) ((X i).mark i) ≤ 2 * (r : ℝ) :=
    (hdist i hi a ha b hb).2.trans (by gcongr; exact (hl _ (Finset.mul_mem_mul ha hb)).2)
  let Z := fun i => markOrbit (G := G) i (X i)
  let π := fun a : G => MulAction.toPerm (β := I) a⁻¹
  refine hdet I Z π good v h₁ h₂ ?_ (hbad.trans (by nlinarith)) ?_ ?_ ?_ ?_
  · intro i
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
  · intro i hi a ha b hb
    change dist ((X i).mark ((a * b)⁻¹ • i)) ((X i).mark ((1 : G)⁻¹ • i)) ^ 2 ≤ _
    rw [inv_one, one_smul]
    exact pow_le_pow_left₀ dist_nonneg (hdist i hi a ha b hb).2 2
  · intro i hi a ha hka
    have he := hh i hi _ (hc i) _ (hmemb i a ha) ⟨a, hhop a (hsub a ha) hka, rfl⟩
    change dist ((X i).mark ((1 : G)⁻¹ • i)) ((X i).mark (a⁻¹ • i)) ^ 2 ≤ _
    rw [inv_one, one_smul]
    nlinarith [pow_le_pow_left₀ dist_nonneg he 2]
  · intro i hi a ha hi' u hu w hw
    let z (i : I) (b : G) (hb : b ∈ S) (s : S) : N i :=
      ⟨(b * s.val)⁻¹ • i, mem_ball i (hmem _ (Finset.mul_mem_mul hb s.property))⟩
    have hz (i : I) (hi : i ∈ good) (b : G) (hb : b ∈ S) :
        Realized (fun s : S => (Z i).mark (b * s.val)) (P i ∘ Tensor.place (z i b hb)) D := by
      apply (hX i).2 S (z i b hb) D hD
      intro s t
      have hh := dist_triangle ((X i).mark ((b * s.val)⁻¹ • i)) ((X i).mark i)
        ((X i).mark ((b * t.val)⁻¹ • i))
      rw [dist_comm ((X i).mark i)] at hh
      change dist ((X i).mark ((b * s.val)⁻¹ • i)) ((X i).mark ((b * t.val)⁻¹ • i)) ≤ 4 * r + 1
      linarith [hrad i hi b hb s s.property, hrad i hi b hb t t.property]
    have heq : Subtype.val ∘ z i a ha = Subtype.val ∘ z (π a i) 1 hS := by
      ext s
      simp [z, π, mul_smul]
    refine htest _ _ (hz i hi a ha) (hz _ hi' 1 hS) ?_ u hu w hw
    intro A hA
    by_cases h0 : A = 0
    · simp [h0, Tensor.place_zero, price_zero (hP i), price_zero (hP (π a i)), hη.le]
    have htA := Finset.mem_erase.mpr ⟨h0, hA⟩
    have hL := (ht i hi).2.2 (z i a ha) A htA
    have hR := (ht _ hi').2.2 (z _ 1 hS) A htA
    rw [heq] at hL
    rw [abs_le] at hL hR ⊢
    simp only [Function.comp_apply]
    constructor <;> linarith
  · intro i hi
    have hval := (ht i hi).1 ⟨i, hc i⟩ ⟨_, hmemb i g hg⟩ rfl rfl
    rw [(hX i).1, abs_le] at hval
    have hd' := hrad i hi 1 hS g hg
    rw [one_mul, dist_comm] at hd'
    let d := dist ((X i).mark i) ((X i).mark (g⁻¹ • i))
    change -ρ ≤ v i - d ∧ v i - d ≤ ρ at hval
    have hd0 : 0 ≤ d := dist_nonneg
    have hv' : |v i| ≤ d + ρ := abs_le.mpr ⟨by linarith, by linarith⟩
    have hs := pow_le_pow_left₀ (abs_nonneg _) hv' 2
    rw [sq_abs] at hs
    have hprod : ρ * (2 * d + ρ) ≤ δ := (mul_le_mul_of_nonneg_left
      (show 2 * d + ρ ≤ D + 3 by unfold D d; linarith) hp.le).trans hd
    simp only [Z, markOrbit, inv_one, one_smul]
    change _ ≤ d ^ 2 + δ
    linarith

end OAI.LinearAlgebra.MatrixExponent.Routing
end
