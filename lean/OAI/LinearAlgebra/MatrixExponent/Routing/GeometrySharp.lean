import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.Analysis.SpecificLimits.Basic
import OAI.LinearAlgebra.MatrixExponent.Prices.Finite
import OAI.LinearAlgebra.MatrixExponent.Prices.WireRecovery
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryComparison
import OAI.LinearAlgebra.MatrixExponent.Routing.PartitionsPlane
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryPrices
import OAI.LinearAlgebra.MatrixExponent.Prices.Fields
import OAI.LinearAlgebra.MatrixExponent.Prices.MovingForms
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Seating
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

section
/-!
# Uniform displacement from incidence

Average the plane sites over the incident planes at each line. The
projective estimate and the variance inequality then bound the mean
square deviation of these line sites by 1/18 of the line-plane energy.
The single-plane displacement estimate loses 160/9. Their product
80/81 is strictly less than one, so iteration gives a common fixed point.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Classical Topology
open Filter

variable {Y E L P D A B G : Type*} [MetricSpace Y]

private theorem expect_fiber [Fintype E] [Fintype L]
    (l : E → L) (f g : E → ℝ)
    (h : ∀ i, (𝔼 e : {e // l e = i}, f e.val) ≤ (𝔼 e : {e // l e = i}, g e.val)) :
    (𝔼 e, f e) ≤ (𝔼 e, g e) := by
  simp only [Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Fintype.sum_fiberwise l f, ← Fintype.sum_fiberwise l g]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Fintype.card_mul_expect] using
    mul_le_mul_of_nonneg_left (h i) (show 0 ≤ (Fintype.card {e // l e = i} : ℝ) by positivity)

variable [Group G] [MulAction G Y] [IsIsometricSMul G Y]
  [Fintype P] [Nonempty P] [Fintype L] [Nonempty L] [Fintype D] [Nonempty D]

private def NearPlanes (K : P → Subgroup G) (x : Y) (R : ℝ) : Prop :=
  ∃ z : P → Y, (∀ p, Fixes (K p) (z p)) ∧ (𝔼 p, dist x (z p) ^ 2) ≤ R

/-- One simultaneous update, using two sets of barycenters. -/
private theorem contract [CompleteSpace Y] (C : Comparison Y) (l : P × D → L)
    (hs : Function.Surjective l) (hi : Incidence Y l Prod.fst)
    (H : Subgroup G) (S : L → Subgroup G) (K : P → Subgroup G)
    (h₀ : ∀ i, H ≤ S i) (h₁ : ∀ e, S (l e) ≤ K e.1)
    (hp : ∀ (p : P) (b : Y) (y : L → Y), Fixes H b → (∀ i, Fixes (S i) (y i)) →
      ∃ z, Fixes (K p) z ∧ 9 * dist b z ^ 2 ≤ 160 * (𝔼 d, dist b (y (l (p, d))) ^ 2))
    {x : Y} {R : ℝ} (hx : NearPlanes K x R) :
    ∃ b, NearPlanes K b (80 / 81 * R) ∧ dist x b ^ 2 ≤ 9 * R := by
  obtain ⟨z, hz, hr⟩ := hx
  let u (i : L) := {e : P × D // l e = i}
  have (i : L) : Nonempty (u i) := by
    obtain ⟨e, he⟩ := hs i
    exact ⟨⟨e, he⟩⟩
  choose y hy using (fun i => C.bary (fun e : u i => z e.val.1))
  have hf (i : L) : Fixes (S i) (y i) := by
    intro g hg
    apply (hy i).fixed
    intro e
    exact hz _ g (h₁ e.val (by rwa [e.property]))
  obtain ⟨b, hb⟩ := C.bary y
  have hb' : Fixes H b := fun g hg => hb.fixed (fun i => hf i g (h₀ i hg))
  let E := 𝔼 e : P × D, dist (y (l e)) (z e.1) ^ 2
  let X := fun a : Y => 𝔼 e : P × D, dist a (y (l e)) ^ 2
  let Z := fun a : Y => 𝔼 p : P, dist a (z p) ^ 2
  have hZ (a : Y) : (𝔼 e : P × D, dist a (z e.1) ^ 2) = Z a := by
    rw [expect_pair]
    simp only [Fintype.expect_const, Z]
  have hv (a : Y) : E + X a ≤ Z a := by
    rw [← hZ]
    unfold E X
    rw [← Finset.expect_add_distrib]
    apply expect_fiber l
    intro i
    have he (e : u i) : l e.val = i := e.property
    simp only [he, Finset.expect_add_distrib, Fintype.expect_const]
    rw [dist_comm a (y i)]
    exact hy i a
  have hX (a : Y) : 0 ≤ X a := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hh : 9 * (X b + Z b) ≤ 10 * E := by
    rw [← hZ]
    exact hi.estimate z hb
  change Z x ≤ R at hr
  have hE : E ≤ R := by linarith [hv x, hX x]
  have hxb : 18 * X b ≤ R := by linarith [hv b]
  choose w hw hw' using fun p => hp p b y hb' hf
  refine ⟨b, ⟨w, hw, ?_⟩, ?_⟩
  · have hv' := Finset.expect_le_expect (s := Finset.univ) fun p _ => hw' p
    simp only [← Finset.mul_expect] at hv'
    unfold X at hxb
    rw [expect_pair] at hxb
    linarith only [hxb, hv']
  · have hh' (p : P) : dist x b ^ 2 ≤ 2 * dist x (z p) ^ 2 + 2 * dist b (z p) ^ 2 := by
      rw [dist_comm b]
      exact dist_sq_triangle _ _ _
    have ht := Finset.expect_le_expect (s := Finset.univ) fun p _ => hh' p
    simp only [Fintype.expect_const, Finset.expect_add_distrib, ← Finset.mul_expect] at ht
    change dist x b ^ 2 ≤ 2 * Z x + 2 * Z b at ht
    have hR : 0 ≤ R := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans hr
    linarith [hX b]

private theorem NearPlanes.bound {K : P → Subgroup G} {x : Y} {R : ℝ}
    (h : NearPlanes K x R) (i : P) {g : G} (hg : g ∈ K i) :
    dist x (g • x) ^ 2 ≤ 4 * Fintype.card P * R := by
  obtain ⟨z, hz, hr⟩ := h
  have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ (Fintype.card P : ℝ) by positivity)
  rw [Fintype.card_mul_expect] at hb
  have hd : dist x (z i) ^ 2 ≤ ∑ p, dist x (z p) ^ 2 :=
    Finset.single_le_sum (fun p _ => sq_nonneg (dist x (z p))) (Finset.mem_univ i)
  have ht := dist_sq_triangle x (z i) (g • x)
  have he : dist (z i) (g • x) = dist x (z i) := by
    rw [← hz i g hg, dist_smul, dist_comm, hz i g hg]
  rw [he] at ht
  linarith

/-- Summing the displacements of the contracting placements gives an
absolute bound, independent of the number of planes. -/
private theorem common_fixed [CompleteSpace Y] (K : P → Subgroup G)
    (hgen : iSup K = ⊤) (x : Y) (hx : NearPlanes K x 1)
    (hc : ∀ (x : Y) (R : ℝ), NearPlanes K x R →
      ∃ b, NearPlanes K b (80 / 81 * R) ∧ dist x b ^ 2 ≤ 9 * R) :
    ∃ b, (∀ g : G, g • b = b) ∧ dist x b ≤ 600 := by
  let r : ℝ := 80 / 81
  let s : ℝ := 199 / 200
  have hr : 0 ≤ r := by norm_num [r]
  have hr' : r < 1 := by norm_num [r]
  have hs : 0 ≤ s := by norm_num [s]
  have hs' : s < 1 := by norm_num [s]
  have hrs : r ≤ s ^ 2 := by norm_num [r, s]
  let S (n : ℕ) := {y : Y // NearPlanes K y (r ^ n)}
  have hnext (n : ℕ) (a : S n) : ∃ b : S (n + 1), dist a.val b.val ≤ 3 * s ^ n := by
    obtain ⟨b, hb, hd⟩ := hc _ _ a.property
    refine ⟨⟨b, by rwa [pow_succ']⟩, ?_⟩
    have hh : r ^ n ≤ (s ^ n) ^ 2 := by
      rw [pow_right_comm]
      exact pow_le_pow_left₀ hr hrs n
    change dist a.val b ≤ _
    nlinarith [pow_nonneg hs n]
  choose next hn using hnext
  let u : ∀ n, S n := Nat.rec ⟨x, by rwa [pow_zero]⟩ next
  let y n := (u n).val
  have hm (n : ℕ) : dist (y n) (y (n + 1)) ≤ 3 * s ^ n := hn n (u n)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric s 3 hs' hm)
  have hfix : iSup K ≤ MulAction.stabilizer G b := by
    apply iSup_le
    intro i g hg
    have hl : Tendsto (fun n => dist (y n) (g • y n) ^ 2) atTop (𝓝 (dist b (g • b) ^ 2)) :=
      (hb.dist (hb.const_smul g)).pow 2
    have hu : Tendsto (fun n => 4 * (Fintype.card P : ℝ) * r ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr').const_mul (4 * Fintype.card P : ℝ)
    have hle := le_of_tendsto_of_tendsto' hl hu (fun n => (u n).property.bound i hg)
    exact (dist_eq_zero.mp (by nlinarith : dist b (g • b) = 0)).symm
  rw [hgen] at hfix
  refine ⟨b, fun g => hfix (Subgroup.mem_top g), ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto₀ s 3 hs' hm hb
  change dist x b ≤ 3 / (1 - s) at hd
  norm_num [s] at hd
  exact hd

/-- Uniform displacement. The only group-specific inputs are generation,
nesting, and the affine partition action on each plane. -/
theorem uniform_displacement [Fintype A] [Nonempty A] [CompleteSpace Y]
    (C : Comparison Y) (l : P × D → L) (hs : Function.Surjective l)
    (a : A × D → B) (hi : Incidence Y l Prod.fst) (ha : Incidence Y Prod.fst a)
    (H : Subgroup G) (S : L → Subgroup G) (K : P → Subgroup G)
    (h₀ : ∀ i, H ≤ S i) (h₁ : ∀ e, S (l e) ≤ K e.1) (hgen : iSup K = ⊤)
    (hplane : ∀ p, ∃ σ, PlaneAction H (K p) (fun d => S (l (p, d))) a σ)
    (x : Y) (hx : ∀ p g, g ∈ K p → dist x (g • x) ≤ 1) :
    (∃ b, (∀ g : G, g • b = b) ∧ dist x b ≤ 600) ∧
      ∀ g : G, dist x (g • x) ≤ 1200 := by
  have hstart : NearPlanes K x 1 := by
    have hz (p : P) : ∃ z, Fixes (K p) z ∧ dist x z ^ 2 ≤ 1 := by
      obtain ⟨z, hf, hd⟩ := C.orbit (K p) x 1 (fun g hg => by
        simpa using pow_le_pow_left₀ dist_nonneg (hx p g hg) 2)
      exact ⟨z, hf, by linarith⟩
    choose z hf hd using hz
    exact ⟨z, hf, Finset.expect_le Finset.univ_nonempty (fun p _ => hd p)⟩
  obtain ⟨b, hb, hd⟩ := common_fixed K hgen x hstart (by
    intro x R hr
    refine contract C l hs hi H S K h₀ h₁ ?_ hr
    intro p b y hb hy
    obtain ⟨σ, hσ⟩ := hplane p
    exact hσ.fixed C ha hb (fun d => y (l (p, d))) (fun d => hy _))
  refine ⟨⟨b, hb, hd⟩, ?_⟩
  intro g
  have ht := dist_triangle x b (g • x)
  have he : dist b (g • x) = dist x b := by rw [← hb g, dist_smul, dist_comm, hb]
  linarith

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Variance survives adjoining a spectral site

The barycenter belongs to the closure of the finite geodesic terms.
Their costs are identical in any two realizations of the same prices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped BigOperators Classical
variable {F A Y Z : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]
  [MetricSpace Y] [MetricSpace Z]

omit [DecidableEq A] in
theorem Bary.mem_closure {x : A → Y} {o : Y} (ho : Bary x o) (C : Comparison Y) :
    o ∈ closure (Set.range (Term.eval C x)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((𝔼 i, dist o (x i) ^ 2) / ε ^ 2)
  rw [div_lt_iff₀ (by positivity)] at hn
  by_contra! bad
  have h (u : Fin (n + 1) → A) : ε ^ 2 ≤ dist (sampleMean C.seg n (x ∘ u)) o ^ 2 := by
    apply pow_le_pow_left₀ hε.le
    rw [dist_comm]
    apply bad
    exact ⟨sampleMean Term.seg n (Term.mark ∘ u),
      sampleMean_map Term.seg C.seg (Term.eval C x) (fun _ _ _ => rfl) n _⟩
  have he := Finset.expect_le_expect (s := Finset.univ) (fun u _ => h u)
  rw [Fintype.expect_const] at he
  linarith only [sampleMean_error C ho n, hn, sq_nonneg ε,
    mul_le_mul_of_nonneg_left he (show 0 ≤ (n : ℝ) + 1 by positivity)]

private theorem ExtendsAt.eq_terms {x : A → Y} {y : A → Z} {P : Tensor F A → ℝ}
    (hx : ExtendsAt P x) (hy : ExtendsAt P y) (C : Comparison Y) (C' : Comparison Z)
    (s t : Term A) : dist (s.eval C x) (t.eval C x) ^ 2 = dist (s.eval C' y) (t.eval C' y) ^ 2 := by
  obtain ⟨B, hB⟩ := (Set.finite_range (fun i : A × A =>
    max (dist (x i.1) (x i.2)) (dist (y i.1) (y i.2)))).bddAbove
  let D := max B 1
  have hd : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have h (i j : A) : max (dist (x i) (x j)) (dist (y i) (y j)) ≤ D :=
    (hB ⟨(i, j), rfl⟩).trans (le_max_left _ _)
  apply sub_eq_zero.mp
  apply abs_nonpos_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T, δ, hδ, hT⟩ := finite_terms_tests F {s, t} D hε
  rw [zero_add]
  exact hT C C' (hx D hd (fun i j => (le_max_left _ _).trans (h i j)))
    (hy D hd (fun i j => (le_max_right _ _).trans (h i j))) (by simp [hδ.le])
    s (by simp) t (by simp)

omit [Nonempty A] [DecidableEq A] in
private theorem Bary.le_sum {x : A → Y} {o : Y} (h : Bary x o) (z : Y) :
    (∑ i, dist o (x i) ^ 2) ≤ ∑ i, dist z (x i) ^ 2 := by
  have he := le_trans (le_add_of_nonneg_right (sq_nonneg _)) (h z)
  simpa only [Fintype.card_mul_expect] using
    mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) (Fintype.card A))

theorem ExtendsAt.variance [CompleteSpace Z] {x : A → Y} {y : A → Z}
    {P : Tensor F A → ℝ} (hx : ExtendsAt P x) (hy : ExtendsAt P y)
    (C : Comparison Y) (C' : Comparison Z) {o : Y} (ho : Bary x o) (z : Z) :
    (∑ i, dist o (x i) ^ 2) ≤ ∑ i, dist z (y i) ^ 2 := by
  obtain ⟨b, hb⟩ := C'.bary y
  let T := {w : Z | (∑ i, dist o (x i) ^ 2) ≤ ∑ i, dist w (y i) ^ 2}
  have hc : IsClosed T := isClosed_le continuous_const (by fun_prop)
  have hs : Set.range (Term.eval C' y) ⊆ T := by
    rintro _ ⟨a, rfl⟩
    exact (ho.le_sum (a.eval C x)).trans_eq (Finset.sum_congr rfl fun i _ =>
      hx.eq_terms hy C C' a (.mark i))
  exact (closure_minimal hs hc (hb.mem_closure C')).trans (hb.le_sum z)

private theorem ExtendsAt.ordinary [Nontrivial A] {x : A → Y} {P : Tensor F A → ℝ}
    (h : ExtendsAt P x) : ∃ D, P ∈ Tensor.ordinary F A D := by
  obtain ⟨d, hd, f, hf, he, _⟩ := h.prices x
  let Q := Tensor.values d f
  have heq : P = Q ∘ Tensor.place Sum.inl := by
    funext a
    apply mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    unfold Q
    rw [he, Function.comp_apply, Tensor.place_inl, Tensor.values, mul_assoc,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
  have hh : Q ∈ Tensor.ordinary F (A ⊕ A) d := ⟨d, ⟨hd, le_rfl⟩, f, hf, rfl⟩
  rw [heq]
  refine ⟨d * Fintype.card A, Tensor.ordinary_restrict hh Sum.inl (fun a b => ?_)⟩
  exact (mul_le_mul_of_nonneg_left (Tensor.dist_le_one _ hf _ _) hd).trans_eq (mul_one d)

theorem SpectralSpace.variance_test (S : SpectralSpace F Y) (C : Comparison Y) : VarianceTest F Y := by
  intro A _ _ _ x o ho
  obtain ⟨P, _, hP⟩ := S A x
  change ExtendsAt P x at hP
  obtain ⟨_, d, ⟨hd, _⟩, f, hf, rfl⟩ := hP.ordinary
  refine ⟨d, hd, f, hf, hP, ?_⟩
  intro g hg he
  have hh : Tensor.values d g ∈ Tensor.ordinary F (A ⊕ Unit) d := ⟨d, ⟨hd, le_rfl⟩, g, hg, rfl⟩
  obtain ⟨Z, _, _, y, C', _, hy⟩ := realize (spectralComparison F) hh
  have heq : Tensor.values d g ∘ Tensor.place (Sum.inl : A → A ⊕ Unit) = Tensor.values d f := by
    funext a
    simp only [Function.comp_apply, Tensor.place_inl, Tensor.values, he]
  have hx : ExtendsAt (Tensor.values d f) (y ∘ Sum.inl) := by
    rw [← heq]
    exact hy.2 A Sum.inl
  refine (hP.variance hx C C' ho (y (.inr ()))).trans_eq (Finset.sum_congr rfl ?_)
  intro i _
  rw [Function.comp_apply, dist_comm, ← hy.1]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Generation by plane motions

A motion in a direct sum of subspaces factors into three motions along
the two summands. The factors act simultaneously across all instances.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {k V J : Type} [Field k] [AddCommGroup V] [Module k V]

private def sumChart (S T : Submodule k V) (h : Disjoint S T) :
    S × T ≃ ↥(S ⊔ T) :=
  Equiv.ofBijective (fun p => ⟨p.1 + p.2, Submodule.add_mem_sup p.1.2 p.2.2⟩) (by
    constructor
    · intro x y he
      have eqn : (x.1 : V) + x.2 = (y.1 : V) + y.2 := congrArg Subtype.val he
      have hx : (x.1 : V) - y.1 = (y.2 : V) - x.2 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm (y.2 : V)]
        exact eqn
      have hz := Submodule.disjoint_def.mp h _ (S.sub_mem x.1.2 y.1.2)
        (hx.symm ▸ T.sub_mem y.2.2 x.2.2)
      exact Prod.ext (Subtype.ext (sub_eq_zero.mp hz))
        (Subtype.ext (sub_eq_zero.mp (hx.symm.trans hz)).symm)
    · intro z
      obtain ⟨s, t, he⟩ := Submodule.mem_sup'.mp z.2
      exact ⟨(s, t), Subtype.ext he⟩)

variable [Fintype V] (I A : J → Type) [∀ j, Fintype (I j)] [∀ j, Fintype (A j)]

variable {G : Type} [Group G] (M : PermSystem (Labels V I A) G)

private lemma motion_sup (S T : Submodule k V) (h : Disjoint S T) :
    M.pull (motion I A (S ⊔ T)) ≤ M.pull (motion I A S) ⊔ M.pull (motion I A T) := by
  classical
  obtain ⟨D, hd⟩ := (S ⊔ T).exists_isCompl
  let e := (D.prodEquivOfIsCompl (S ⊔ T) hd.symm).symm
  let f := e.toEquiv.trans ((Equiv.refl D).prodCongr (sumChart S T h).symm)
  let c (j : J) : Labels V I A j ≃ (I j → D) × ((I j → S) × ((I j → T) × A j)) :=
    { toFun := fun x => (fun i => (f (x.1 i)).1, fun i => (f (x.1 i)).2.1,
        fun i => (f (x.1 i)).2.2, x.2)
      invFun := fun y => (fun i => f.symm (y.1 i, y.2.1 i, y.2.2.1 i), y.2.2.2)
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  have read (j : J) (x : Labels V I A j) (i : I j) :
      x.1 i = ((c j x).1 i : V) + (((c j x).2.1 i : V) + ((c j x).2.2.1 i : V)) :=
    (f.symm_apply_apply (x.1 i)).symm
  intro g hg
  have fixed (t : M.World) (j : J) (x : Labels V I A j) :
      (c j (M.read t g j x)).1 = (c j x).1 := by
    funext i
    change (e ((M.read t g j x).1 i)).1 = (e (x.1 i)).1
    have hz : (e ((M.read t g j x).1 i - x.1 i)).1 = 0 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _ hd.symm).mpr (hg t j x i)
    simpa only [map_sub, Prod.fst_sub, sub_eq_zero] using hz
  obtain ⟨u, v, w, he, hu, hv, hw⟩ := M.factor c g fixed
  have outer (z : G)
      (hz : ∀ t j x, (c j (M.read t z j x)).1 = (c j x).1 ∧ (c j (M.read t z j x)).2.1 = (c j x).2.1) :
      z ∈ M.pull (motion I A T) := by
    intro t j x i
    rw [read j (M.read t z j x) i, read j x i, (hz t j x).1, (hz t j x).2,
      add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    exact T.sub_mem ((c j (M.read t z j x)).2.2.1 i).2 ((c j x).2.2.1 i).2
  have middle : v ∈ M.pull (motion I A S) := by
    intro t j x i
    rw [read j (M.read t v j x) i, read j x i, (hv t j x).1, (hv t j x).2,
      add_sub_add_left_eq_sub, add_sub_add_right_eq_sub]
    exact S.sub_mem ((c j (M.read t v j x)).2.1 i).2 ((c j x).2.1 i).2
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (outer u hu))
    (Subgroup.mem_sup_left middle)) (Subgroup.mem_sup_right (outer w hw))

/-- Plane motions generate any group closed under the required factorizations. -/
theorem PermSystem.motion_generate (h : 2 ≤ Module.finrank k V) :
    (⨆ P : VPlane k V, M.pull (motion I A P.1)) = ⊤ := by
  classical
  let H := ⨆ P : VPlane k V, M.pull (motion I A P.1)
  have plane (P : VPlane k V) : M.pull (motion I A P.1) ≤ H := le_iSup (fun P => M.pull (motion I A P.1)) P
  have spans (s : Finset V) : M.pull (motion I A (Submodule.span k (s : Set V))) ≤ H := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨P⟩ := flat_nonempty h
      rw [Finset.coe_empty, Submodule.span_empty]
      exact (M.pull_mono (motion_mono I A bot_le)).trans (plane P)
    | @insert x s _ ih =>
      rw [Finset.coe_insert, Submodule.span_insert]
      by_cases hx : x ∈ Submodule.span k (s : Set V)
      · rwa [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)]
      · have hn : x ≠ 0 := fun he => hx (he.symm ▸ Submodule.zero_mem _)
        let p : VPoint k V := ⟨_, finrank_span_singleton hn⟩
        obtain ⟨⟨P, d⟩, hd⟩ := surjective_flagPoint h p
        have hl : p.1 ≤ P.1 := by rw [← hd]; exact dir_le P d
        exact (motion_sup I A M _ _ (Submodule.disjoint_span_singleton_of_notMem hx).symm).trans
          (sup_le ((M.pull_mono (motion_mono I A hl)).trans (plane P)) ih)
  have ht := spans Finset.univ
  rw [Finset.coe_univ, Submodule.span_univ] at ht
  exact top_unique fun g _ => ht (fun _ _ _ _ => Submodule.mem_top)

theorem motion_generate (h : 2 ≤ Module.finrank k V) :
    (⨆ P : VPlane k V, motion I A P.1) = ⊤ := by
  simpa only [PermSystem.full_pull] using
    PermSystem.motion_generate I A (PermSystem.full (Labels V I A)) h

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! Finite transport bounds at every block of every collision. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Motion

open Finset Sphere Spectral
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] (a : A → Fin 2 → F)

theorem regular_parameter [Infinite F] (ha : Function.Injective a) :
    ∃ s : F, denominator (directions a) s 1 ≠ 0 ∧
      Function.Injective (fun i => position (a i) s 1) := by
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset ((directions a).eraseNone)
  have hd : denominator (directions a) (-v) 1 ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun d hd => ?_
    cases d with
    | none => exact one_ne_zero
    | some t =>
      have ht : t ≠ v := fun he => hv (by simpa [he] using hd)
      simpa [linearFactor, sub_eq_add_neg, add_comm] using sub_ne_zero.mpr ht
  refine ⟨-v, hd, fun i j h => ?_⟩
  by_contra hi
  have he : projection (a i) (some v) = projection (a j) (some v) := by
    simpa [projection, position, mul_comm, sub_eq_add_neg, add_comm] using h
  have e := eq_through (k := (some v, projection (a j) (some v))) (ha.ne hi) he rfl
  have he' : some v = pole (a i) (a j) := congrArg Prod.fst e
  exact hv (by simpa [← he'] using pole_mem a i j)

theorem degree_le (e : A → ℕ) :
    2 * degree a e ≤ ((directions a).card - 1) * ∑ i, e i := by
  unfold degree
  rw [mul_left_comm]
  exact Nat.mul_le_mul_left _ (by omega)

def countBound (e : A → ℕ) := ((directions a).card + 1) * (2 * degree a e + 2) ^ Fintype.card A

variable [DecidableEq A] [Nonempty A] {Y : Type*} [MetricSpace Y]
variable {P : Tensor F A → ℝ} {x : A → Y}

theorem finite_transport (hx : ExtendsAt P x) (s : F) (hs : denominator (directions a) s 1 ≠ 0) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ e : A → ℕ, ∃ b : Option F × F → ℕ,
      (∑ k ∈ blocks a, b k) ≤ 2 * degree a e ∧
      ∀ k ∈ blocks a, ∀ m o : Y,
        spherePrice P (fun i => position (a i) s 1) e ≤
          d * Real.log (countBound a e) + dist o m * width (b k) +
            ∑ i, dist (if i ∈ pointsOn a k then m else o) (x i) * width (e i) := by
  obtain ⟨d, hd, hspan⟩ := hx.span
  refine ⟨d, hd, fun e => ?_⟩
  let X := fun i => Level 1 (e i)
  let p := tablePrice X P
  let T := form a e s
  let M := 2 * degree a e + 1
  let C := countBound a e
  change ∃ b : Option F × F → ℕ, _ ∧ ∀ k ∈ blocks a, ∀ m o : Y, p T ≤ _
  by_cases hp : 0 < p T
  swap
  · refine ⟨fun _ => 0, by simp, fun k _ m o => (le_of_not_gt hp).trans ?_⟩
    unfold width
    have := entropy_pos
    positivity
  let bad := (menu a e M).filter fun v => p v + d * Real.log C < p T
  have hbad : bad.card ≤ C := calc
    _ ≤ (menu a e M).card := card_filter_le _ _
    _ ≤ _ := (menu_size a e M).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  let W := Submodule.span F (bad : Set (States 1 e → F))
  have hn : T ∉ W := by
    intro ht
    obtain ⟨v, hv, h⟩ := hspan X T bad hp ht
    have hl : Real.log bad.card ≤ Real.log C :=
      Real.log_le_log (Nat.cast_pos.mpr (card_pos.mpr ⟨v, hv⟩)) (Nat.cast_le.mpr hbad)
    exact (mem_filter.mp hv).2.not_ge (h.trans (add_le_add_right (mul_le_mul_of_nonneg_left hl hd) _))
  obtain ⟨b, hb, hcuts⟩ := select_cuts a e (M := M) (by omega) W s hs hn
  refine ⟨b, hb, fun k hk m o => ?_⟩
  obtain ⟨v, hv, hw, L, R, he, hl, hr⟩ := hcuts k hk
  have h₁ : p T ≤ p v + d * Real.log C := by
    by_contra! hh
    exact hw (Submodule.subset_span (mem_filter.mpr ⟨hv, hh⟩))
  have h₂ : p v ≤ dist o m * width (b k) +
      ∑ i, dist (if i ∈ pointsOn a k then m else o) (x i) * width (e i) :=
    (hx.cut X v (pointsOn a k) L R he hl hr m o).trans
      (add_le_add (mul_le_mul_of_nonneg_left (entropy_bound _) dist_nonneg)
        (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (entropy_bound _) dist_nonneg))
  exact h₁.trans (by linarith only [h₂])

end OAI.LinearAlgebra.MatrixExponent.Routing.Motion
end

/-!
# The limiting widths of collision blocks

The finite fusion terms have polynomially many energy patterns, so their
logarithmic overhead vanishes after normalization. Compactness gives a
single limit for every block, independent of the transport test site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset Filter
open scoped Classical Topology

variable {F A : Type} [Field F] [Fintype A]

theorem width_budget {I J : Type*} (s : Finset I) (t : Finset J)
    (b : I → ℕ) (e : J → ℕ) (D : ℕ) (n : ℝ)
    (h : (∑ i ∈ s, b i) ≤ D * ∑ j ∈ t, e j) :
    (∑ i ∈ s, (width (b i) / n) ^ 2) ≤ D * ∑ j ∈ t, (width (e j) / n) ^ 2 := by
  have he : (∑ i ∈ s, (b i : ℝ)) ≤ D * ∑ j ∈ t, (e j : ℝ) := by exact_mod_cast h
  simp only [div_pow, width_sq, ← sum_div, ← mul_sum]
  rw [← mul_div_assoc, mul_left_comm (D : ℝ)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (sq_nonneg _)) (sq_nonneg _)

private theorem log_limit {f : ℕ → ℕ} {k : ℕ} (h : ∀ᶠ n in atTop, f n ≤ n ^ k) :
    Tendsto (fun n => Real.log (f n) / (n : ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hk : Tendsto (fun n : ℕ => Real.log ((n : ℝ) ^ k) / n) atTop (𝓝 0) := by
    simpa only [Real.log_pow, mul_div_assoc, mul_zero] using hl.const_mul (k : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk
  · exact Eventually.of_forall fun n => by positivity
  filter_upwards [h] with n hn
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  by_cases hf : f n = 0
  · simp only [hf, Nat.cast_zero, Real.log_zero, Real.log_pow]
    positivity
  exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hf) (by exact_mod_cast hn)

theorem Motion.countBound_limit (a : A → Fin 2 → F) (e : ℕ → A → ℕ) {R : ℝ}
    (he : Tendsto (fun n => ∑ i, (width (e n i) / (n : ℝ)) ^ 2) atTop (𝓝 R)) :
    Tendsto (fun n => Real.log (Motion.countBound a (e n)) / (n : ℝ)) atTop (𝓝 0) := by
  have hc := sq_pos_of_pos Sphere.entropy_pos
  let D := (directions a).card
  obtain ⟨K, hK⟩ := exists_nat_gt ((R + 1) / Sphere.entropy ^ 2)
  have he' : ∀ᶠ n in atTop, (∑ i, e n i) ≤ K * n ^ 2 := by
    filter_upwards [he.eventually_le_const (lt_add_one _), eventually_gt_atTop 0] with n h hn
    have hn' : 0 < (n : ℝ) ^ 2 := by positivity
    simp only [div_pow, width_sq, ← sum_div, ← mul_sum] at h
    rw [div_le_iff₀ hn'] at h
    have h' := mul_le_mul_of_nonneg_right ((div_lt_iff₀ hc).mp hK).le hn'.le
    have h'' : (∑ i, (e n i : ℝ)) ≤ K * (n : ℝ) ^ 2 :=
      le_of_mul_le_mul_left (by linarith only [h, h']) hc
    exact_mod_cast h''
  apply log_limit (k := 3 * Fintype.card A + 1)
  filter_upwards [he', eventually_ge_atTop (D + 1), eventually_ge_atTop (D * K + 2)] with n hn hD hK
  have hdeg : 2 * Motion.degree a (e n) + 2 ≤ n ^ 3 := calc
    _ ≤ D * (K * n ^ 2) + 2 := Nat.add_le_add_right
      ((Motion.degree_le a _).trans (Nat.mul_le_mul (Nat.sub_le _ _) hn)) _
    _ ≤ (D * K + 2) * n ^ 2 := by nlinarith [show 1 ≤ n ^ 2 from Nat.one_le_pow 2 n (by omega)]
    _ ≤ n ^ 3 := by rw [pow_succ' n 2]; exact Nat.mul_le_mul_right _ hK
  rw [pow_succ', pow_mul]
  exact Nat.mul_le_mul hD (Nat.pow_le_pow_left hdeg _)

private theorem budget_limit {I : Type*} (s : Finset I) (u : ℕ → I → ℝ) (r : ℕ → ℝ) {R : ℝ}
    (hu : ∀ n i, 0 ≤ u n i) (hb : ∀ n, ∑ i ∈ s, (u n i) ^ 2 ≤ r n)
    (hr : Tendsto r atTop (𝓝 R)) :
    ∃ b : I → ℝ, (∑ i ∈ s, (b i) ^ 2) ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, Tendsto (fun n => u (φ n) i) atTop (𝓝 (b i)) := by
  let f (n : ℕ) (i : ↥s) := u n i.1
  have hh : ∀ᶠ n in atTop, f n ∈ Set.Icc 0 (fun _ => R + 2) := by
    filter_upwards [hr.eventually_le_const (lt_add_one _)] with n hn
    refine ⟨fun i => hu _ _, fun i => ?_⟩
    have hi : (f n i) ^ 2 ≤ R + 1 :=
      ((single_le_sum (fun j _ => sq_nonneg (u n j)) i.2).trans (hb n)).trans hn
    nlinarith only [hi, sq_nonneg (f n i - 1)]
  obtain ⟨v, _, φ, hφ, hv⟩ := isCompact_Icc.tendsto_subseq' hh.frequently
  let b (i : I) := if h : i ∈ s then v ⟨i, h⟩ else 0
  have he (i : I) (hi : i ∈ s) : Tendsto (fun n => u (φ n) i) atTop (𝓝 (b i)) := by
    simpa [b, hi, f] using tendsto_pi_nhds.mp hv ⟨i, hi⟩
  refine ⟨b, ?_, φ, hφ, he⟩
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum s (fun i hi => (he i hi).pow 2))
    (hr.comp hφ.tendsto_atTop) (fun n => hb (φ n))

/-- The unit-mass sphere price profile implies the full collision
budget and the transport inequality on every block. -/
theorem Saturation.collisions {Y : Type*} [MetricSpace Y] [Infinite F]
    (h : Saturation F Y) : CollisionBound F Y := by
  intro A _ a ha hcard x o ho
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨s, hs, hz⟩ := Motion.regular_parameter a ha
  let z i := position (a i) s 1
  obtain ⟨P, hP, e, he, hp⟩ := h x o ho z hz
  obtain ⟨d, hd, hf⟩ := Motion.finite_transport a hP s hs
  choose b hb ht using fun n => hf (e n)
  let D := (directions a).card - 1
  let v n i := width (e n i) / (n : ℝ)
  let u n k := width (b n k) / (n : ℝ)
  let r i := dist o (x i)
  have hr : Tendsto (fun n => ∑ i, (v n i) ^ 2) atTop (𝓝 (∑ i, (r i) ^ 2)) :=
    tendsto_finsetSum _ fun i _ => (he i).pow 2
  have hbudget (n) : ∑ k ∈ blocks a, (u n k) ^ 2 ≤ D * ∑ i, (v n i) ^ 2 :=
    width_budget _ _ _ _ _ _ ((hb n).trans (Motion.degree_le a _))
  obtain ⟨w, hw, φ, hφ, hl⟩ := budget_limit (blocks a) u _
    (fun n k => div_nonneg (width_nonneg _) (Nat.cast_nonneg n)) hbudget (hr.const_mul _)
  refine ⟨w, ?_, fun k hk m => ?_⟩
  · have hD : 1 ≤ (directions a).card := card_pos.mpr ⟨none, mem_insert_self _ _⟩
    simpa only [D, Nat.cast_sub hD, Nat.cast_one] using hw
  let p i := dist (if i ∈ pointsOn a k then m else o) (x i)
  have hsum : Tendsto (fun n => ∑ i, p i * v (φ n) i) atTop (𝓝 (∑ i, p i * r i)) :=
    tendsto_finsetSum _ fun i _ => ((he i).comp hφ.tendsto_atTop).const_mul _
  have hcost := ((Motion.countBound_limit a e hr).comp hφ.tendsto_atTop).const_mul d
  have hineq : ∑ i, r i ^ 2 ≤ (d * 0 + dist o m * w k) + ∑ i, p i * r i := by
    refine le_of_tendsto_of_tendsto' (hp.comp hφ.tendsto_atTop)
      ((hcost.add ((hl k hk).const_mul _)).add hsum) fun n => ?_
    have hn := div_le_div_of_nonneg_right (ht (φ n) k hk m o) ((show (0 : ℝ) ≤ φ n from Nat.cast_nonneg _))
    simpa only [Function.comp_apply, add_div, sum_div, mul_div_assoc] using hn
  have heq : ∑ i, p i * r i = (∑ i ∈ pointsOn a k, r i * dist m (x i)) +
      ∑ i ∈ univ \ pointsOn a k, r i ^ 2 := by
    rw [← sum_sdiff (subset_univ (pointsOn a k)), add_comm]
    congr 1
    · exact sum_congr rfl (fun i hi => by simp [p, hi, mul_comm])
    · exact sum_congr rfl (fun i hi => by simp [p, (mem_sdiff.mp hi).2, r, pow_two])
  rw [heq, ← sum_sdiff (subset_univ (pointsOn a k))] at hineq
  change (∑ i ∈ pointsOn a k, r i ^ 2) ≤ _ + ∑ i ∈ pointsOn a k, r i * dist m (x i)
  linarith only [hineq]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# Bounded displacement for families of permutations

Here the group is the product of all the finite permutation groups. No
restriction on the computation of a permutation family is imposed.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {k V W J : Type} [Field k] [Fintype k] [AddCommGroup V] [Module k V]
  [Fintype V] [AddCommGroup W] [Module k W] [Fintype W]
  (I R : J → Type) [∀ j, Fintype (I j)] [∀ j, Fintype (R j)]

variable (k V W) in
abbrev PermFamilies := ∀ j, Equiv.Perm (Labels V I (Aux k W I R) j)

local notation "𝒢" => PermFamilies k V W I R

/-- Uniform displacement for arbitrary permutation families, conditional
on the two metric incidence inequalities. -/
theorem permutation_displacement {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    [MulAction 𝒢 Y] [IsIsometricSMul 𝒢 Y] (C : Comparison Y)
    (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W)
    (hi : Incidence Y (flagPoint (K := k) (V := V)) Prod.fst)
    (ha : Incidence Y Prod.fst (affineGraph (K := k) (V := W)))
    (x : Y) (hx : ∀ (p : VPlane k V) (g : 𝒢),
      g ∈ motion I (Aux k W I R) p.1 → dist x (g • x) ≤ 1) :
    (∃ b, (∀ g : 𝒢, g • b = b) ∧ dist x b ≤ 600) ∧
      ∀ g : 𝒢, dist x (g • x) ≤ 1200 := by
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let M := motion (k := k) (V := V) I (Aux k W I R)
  exact uniform_displacement C flagPoint (surjective_flagPoint hV) affineGraph hi ha
    (M ⊥) (fun i => M i.val) (fun p => M p.val)
    (fun _ => motion_mono I _ bot_le) (fun e => motion_mono I _ (dir_le e.1 e.2))
    (motion_generate I _ hV) (fun p => motion_plane_action I R p hW) x hx

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# Inputs to the finite detection theorem

Use the affine and projective links over an infinite extension of
the coefficient field. No extension is made to the actual tensors
in the local price tests.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral

variable {k V W : Type} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V]

theorem models_of_shared_price {F L : Type} [Field F] [Field L] [Infinite L] [Algebra F L]
    [Field W] [Fintype W] [Algebra k W] [Algebra k L] [Algebra W L]
    (hsync : Prices.SharedPrice L) (hq : 100 ≤ Fintype.card k) :
    HasModels F (flagPoint (K := k) (V := V)) Prod.fst Prod.fst (affineGraph (K := k) (V := W)) := by
  intro S _ _ _ P hp
  have hm : ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (x : S → Y),
      Comparison Y ∧ SpectralSpace F Y ∧ Represents F P x := by
    rcases hp with rfl | ⟨D, hp⟩
    · exact realize_zero F S
    · exact realize (spectralComparison F) hp
  obtain ⟨Y, _, _, x, C, hY, hr⟩ := hm
  have hs := hY.extend_field L
  have he := (bounded_forms L).extension hsync
  have hh : Saturation L Y :=
    saturation_of_controlled (controlled_of_probes (hs.variance_test C) he (wireProbe L) hs)
  have ht : Secants L Y := CollisionBound.secants (Saturation.collisions hh)
  exact ⟨⟨Y, C, x⟩, hr, Secants.projective ht C hq, Secants.affine ht C hq⟩

variable [AddCommGroup W] [Module k W] [Fintype W] {G J : Type} [Group G]
  (I R : J → Type) [∀ j, Fintype (I j)] [∀ j, Fintype (R j)]
  (M : PermSystem (Labels V I (Aux k W I R)) G)

def PermSystem.planes (p : VPlane k V) : Subgroup G := M.pull (motion I (Aux k W I R) p.val)

theorem PermSystem.rigid (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W) :
    Rigid (hops (M.planes I R)) (flagPoint (K := k) (V := V)) Prod.fst
      Prod.fst (affineGraph (K := k) (V := W)) := by
  intro Y _ _ _ _ C hi ha x hx
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let f := fun s : Submodule k V => M.pull (motion I (Aux k W I R) s)
  exact (uniform_displacement C flagPoint (surjective_flagPoint hV) affineGraph hi ha
    (f ⊥) (fun i => f i.val) (M.planes I R)
    (fun _ => M.pull_mono (motion_mono I _ bot_le))
    (fun e => M.pull_mono (motion_mono I _ (dir_le e.1 e.2)))
    (M.motion_generate I _ hV) (fun p => M.motion_plane_action I R p hW) x
    (fun p g hg => hx g (Set.mem_iUnion.mpr ⟨p, hg⟩))).2

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Sharp incidence estimates under a strict square saving

Points, lines and flags each carry their own uniform probability
measure. Regularity converts the sums over flags to these means.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset
open scoped BigOperators Classical

variable {Y A B E : Type} [MetricSpace Y] [Fintype A] [Fintype B] [Fintype E]

/-- The point barycenter serves both sets of sites. -/
def SharpIncidence (Y : Type) [MetricSpace Y] (q : ℕ) (p : E → A) (l : E → B) : Prop :=
  ∀ (x : A → Y) (y : B → Y) (o : Y), Bary x o →
    (1 - 1 / Real.sqrt q) * ((𝔼 a, dist o (x a) ^ 2) + (𝔼 b, dist o (y b) ^ 2)) ≤
      𝔼 e, dist (x (p e)) (y (l e)) ^ 2

private theorem uniform_expect [DecidableEq A] [Nonempty E] (p : E → A) {j : ℕ}
    (hp : ∀ a, #{i | p i = a} = j) (f : A → ℝ) : (𝔼 e, f (p e)) = 𝔼 a, f a := by
  have hc : (Fintype.card E : ℝ) = j * Fintype.card A := by
    simpa using uniform_sum p hp (fun _ => 1)
  have hj : (j : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hc
    exact (by positivity : (Fintype.card E : ℝ) ≠ 0) hc
  simp only [Fintype.expect_eq_sum_div_card, uniform_sum p hp f, hc, mul_div_mul_left _ _ hj]

private theorem sharp [DecidableEq A] [DecidableEq B] [Nonempty E]
    (C : Comparison Y) (p : E → A) (l : E → B) {j s n q : ℕ} (hq : 0 < q) (hs : 0 < s)
    (hp : ∀ a, #{i | p i = a} = j) (hl : ∀ k, #{i | l i = k} = s) (hd : q * n ≤ j * s)
    (h : ∀ (x : A → Y) o, Bary x o → SecantBound p l x o n) : SharpIncidence Y q p l := by
  intro x y o ho
  rw [← uniform_expect p hp (fun a => dist o (x a) ^ 2),
    ← uniform_expect l hl (fun b => dist o (y b) ^ 2), ← expect_add_distrib]
  simp only [Fintype.expect_eq_sum_div_card, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hr : 0 < Real.sqrt q := by positivity
  rw [show 1 - 1 / Real.sqrt q = (Real.sqrt q - 1) / Real.sqrt q by field_simp, div_mul_eq_mul_div,
    div_le_iff₀ hr, mul_comm _ (Real.sqrt q)]
  exact regular_incidence C p l x y o hs hp hl hd (h x o ho)

variable {F K : Type} [Field F] [Finite F] [Field K] [Fintype K]

private theorem common_field (hc : ringChar K = ringChar F) : Nonempty (Algebra K (AlgebraicClosure F)) := by
  let p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP K p := by unfold p; rw [← hc]; infer_instance
  let _ := ZMod.algebra K p
  let _ := ZMod.algebra (AlgebraicClosure F) p
  exact ⟨(IsAlgClosed.lift : K →ₐ[ZMod p] AlgebraicClosure F).toRingHom.toAlgebra⟩

private theorem secants_of_saving [CompleteSpace Y] (h : omega F < 9 / 4)
    (S : SpectralSpace F Y) (C : Comparison Y) : Secants (AlgebraicClosure F) Y := by
  let L := AlgebraicClosure F
  have hs := S.extend_field L
  have he := (bounded_forms L).extension (shared_of_saving h)
  have hh : Saturation L Y := saturation_of_controlled (controlled_of_probes (hs.variance_test C) he (wireProbe L) hs)
  have ht : Secants L Y := CollisionBound.secants (Saturation.collisions hh)
  exact @ht

/-- Points and lines of projective space over the finite field of
order `q`, in the characteristic of the coefficient field. -/
theorem projective_of_saving [CompleteSpace Y] (h : omega F < 9 / 4)
    (S : SpectralSpace F Y) (C : Comparison Y) (hc : ringChar K = ringChar F)
    {V : Type} [AddCommGroup V] [Module K V] [Finite V] (hV : 2 ≤ Module.finrank K V) :
    SharpIncidence Y (Fintype.card K) (flagPoint (K := K) (V := V)) Prod.fst := by
  let _ := (common_field hc).some
  have : Nonempty (VPlane K V) := flat_nonempty hV
  have hs : Secants (AlgebraicClosure F) Y := secants_of_saving h S C
  refine sharp C flagPoint Prod.fst Fintype.card_pos (Nat.succ_pos _)
    projective_point_degree projective_plane_degree ?_ (Secants.projective_widths hs)
  rw [Nat.mul_comm (Fintype.card K)]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_succ _)

/-- Points in the affine plane of a finite extension and lines in
the `q+1` directions defined over the base field. -/
theorem affine_of_saving [CompleteSpace Y] (h : omega F < 9 / 4)
    (S : SpectralSpace F Y) (C : Comparison Y) (hc : ringChar K = ringChar F)
    {W : Type} [Field W] [Fintype W] [Algebra K W] :
    SharpIncidence Y (Fintype.card K) Prod.fst (affineGraph (K := K) (V := W)) := by
  let _ := (common_field hc).some
  let _ : Algebra W (AlgebraicClosure F) :=
    (IsAlgClosed.lift : W →ₐ[K] AlgebraicClosure F).toRingHom.toAlgebra
  have hs : Secants (AlgebraicClosure F) Y := secants_of_saving h S C
  refine sharp C Prod.fst affineGraph Fintype.card_pos Fintype.card_pos
    affine_point_degree affine_line_degree ?_ (Secants.affine_widths hs)
  exact Nat.mul_le_mul_right _ (Nat.le_succ _)

end OAI.LinearAlgebra.MatrixExponent.Routing
end
