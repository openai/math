import OAI.LinearAlgebra.MatrixExponent.Prices.Fields
import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Prices.Finite
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.VecNotation
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.ScaleSlope
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryComparison
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryPrices
import OAI.LinearAlgebra.MatrixExponent.Prices.MovingForms
import OAI.LinearAlgebra.MatrixExponent.Prices.WireRecovery

/-!
# Compatible ordinary prices

A single choice of prices on all finite placements permits comparing
tests that use different subsets of sites. Repeated marks are allowed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices

open Spectral

structure Atlas (K : Type) (X : Type*) [Field K] [PseudoMetricSpace X] where
  price {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → X) : Tensor K S → ℝ
  valid {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (v : S → X) :
    ∃ D, price v ∈ Tensor.ordinary K S D
  wire {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (v : S → X) (i j : S) :
    price v (Tensor.wire K i j 2) = dist (v i) (v j)
  place {S T : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T] (v : T → X) (f : S → T) :
    price (v ∘ f) = price v ∘ Tensor.place f

namespace Atlas
variable {K S T : Type} [Field K] [Fintype S] [DecidableEq S]

theorem sum_nontrivial (S T : Type) [Nonempty S] [Nonempty T] : Nontrivial (S ⊕ T) :=
  ⟨.inl (Classical.arbitrary S), .inr (Classical.arbitrary T), by simp⟩

section Pseudo
variable {X : Type*} [PseudoMetricSpace X] (A : Atlas K X)

theorem bounded [Nontrivial S] (x : S → X) {E : ℝ}
    (he : ∀ i j, dist (x i) (x j) ≤ E) :
    A.price x ∈ Tensor.ordinary K S (E * Fintype.card S) := by
  obtain ⟨D, hD⟩ := A.valid x
  have h := Tensor.ordinary_restrict hD id (fun i j => (A.wire x i j).le.trans (he i j))
  simpa only [Function.comp_def, Tensor.place_id] using h

theorem congr [Nonempty S] (x y : S → X) (h : ∀ i, dist (x i) (y i) = 0) :
    A.price x = A.price y := by
  let _ := sum_nontrivial S S
  let z := Sum.elim x y
  obtain ⟨D, d, hd, f, hf, he⟩ := A.valid z
  change A.price (z ∘ Sum.inl) = A.price (z ∘ Sum.inr)
  rw [A.place, A.place, he]
  funext B
  change Tensor.values d f (Tensor.place Sum.inl B) = Tensor.values d f (Tensor.place Sum.inr B)
  by_cases hz : d = 0
  · simp [Tensor.values, hz]
  have hh (i : S) : Tensor.dist f (.inl i) (.inr i) = 0 := by
    have e := (A.wire z (.inl i) (.inr i)).trans (h i)
    rw [he] at e
    exact (mul_eq_zero.mp e).resolve_left hz
  rw [Tensor.values, Tensor.values, Tensor.price_place_eq f hf Sum.inl Sum.inr hh]

def pullback {Y : Type*} [PseudoMetricSpace Y] (f : Y → X)
    (h : ∀ a b, dist (f a) (f b) = dist a b) : Atlas K Y where
  price v := A.price (f ∘ v)
  valid v := A.valid (f ∘ v)
  wire v i j := (A.wire (f ∘ v) i j).trans (h _ _)
  place v g := A.place (f ∘ v) g

end Pseudo

variable {X : Type*} [MetricSpace X] (A : Atlas K X) [Nonempty S]

theorem realized (x : S → X) {D : ℝ} (hd : ∀ i j, dist (x i) (x j) ≤ D) :
    Routing.Realized x (A.price x) D := by
  refine ⟨hd, fun U _ _ _ y hy => ?_⟩
  let _ := sum_nontrivial S U
  let z := Sum.elim x y
  refine ⟨A.price z, A.bounded z hy, fun B => ?_, A.wire z⟩
  rw [← Tensor.place_inl]
  exact congrFun (A.place z Sum.inl).symm B

include A in
theorem space : Routing.SpectralSpace K X :=
  fun _ _ _ _ x => ⟨A.price x, A.wire x, fun _ _ h => A.realized x h⟩

theorem represents (x : S → X) : Routing.Represents K (A.price x) x := by
  refine ⟨A.wire x, fun _ _ _ _ z _ _ h => ?_⟩
  rw [← A.place]
  exact A.realized _ h

end Atlas
end OAI.LinearAlgebra.MatrixExponent.Prices
end

/-! # A common limit for all finite placement prices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas

open Spectral Filter Topology
variable {K : Type} {X I : Type*} [Field K] [PseudoMetricSpace X]

theorem of_limit (l : Ultrafilter I)
    (P : ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S], (S → X) → I → Tensor K S → ℝ)
    (hv : ∀ {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (x : S → X),
      ∃ D, ∀ᶠ i in (l : Filter I), P x i ∈ Tensor.ordinary K S D)
    (hw : ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (x : S → X) (a b : S),
      Tendsto (fun i => P x i (Tensor.wire K a b 2)) (l : Filter I) (𝓝 (dist (x a) (x b))))
    (hc : ∀ {S T : Type} [Fintype S] [DecidableEq S] [Nonempty S]
      [Fintype T] [DecidableEq T] [Nonempty T] (x : T → X) (y : S → T) (i : I),
      P (x ∘ y) i = P x i ∘ Tensor.place y) :
    ∃ A : Atlas K X, ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (x : S → X),
      Tendsto (P x) (l : Filter I) (𝓝 (A.price x)) := by
  have lim {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (x : S → X) :
      ∃ D, ∃ Q ∈ Tensor.ordinary K S D, Tendsto (P x) (l : Filter I) (𝓝 Q) := by
    obtain ⟨D, hD⟩ := hv x
    exact ⟨D, (Tensor.compact_ordinary _).ultrafilter_le_nhds' (l.map (P x)) (Filter.mem_map.mpr hD)⟩
  have existsQ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (x : S → X) :
      ∃ Q, Tendsto (P x) (l : Filter I) (𝓝 Q) := by
    let _ := sum_nontrivial S S
    let z := Sum.elim x x
    obtain ⟨_, Q, _, hQ⟩ := lim z
    refine ⟨Q ∘ Tensor.place Sum.inl, tendsto_pi_nhds.mpr fun B => ?_⟩
    exact (tendsto_pi_nhds.mp hQ (Tensor.place Sum.inl B)).congr'
      (Eventually.of_forall fun i => congrFun (hc z Sum.inl i).symm B)
  let A : Atlas K X :=
    { price := fun x => (existsQ x).choose
      valid := fun x => by
        obtain ⟨D, Q, hQ, h⟩ := lim x
        exact ⟨D, tendsto_nhds_unique h (existsQ x).choose_spec ▸ hQ⟩
      wire := fun x a b => tendsto_nhds_unique
        (tendsto_pi_nhds.mp (existsQ x).choose_spec _) (hw x a b)
      place := fun x y => by
        funext B
        apply tendsto_nhds_unique (tendsto_pi_nhds.mp (existsQ (x ∘ y)).choose_spec B)
        exact (tendsto_pi_nhds.mp (existsQ x).choose_spec (Tensor.place y B)).congr'
          (Eventually.of_forall fun i => congrFun (hc x y i).symm B) }
  exact ⟨A, fun x => (existsQ x).choose_spec⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-! Compatible prices on a limit of rescaled finite placements. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
open Spectral Filter Topology
variable {K : Type} [Field K] {X I : Type*} [PseudoMetricSpace X]

theorem scaled_limit (l : Ultrafilter I) (Y : I → Type*) [∀ i, PseudoMetricSpace (Y i)]
    (A : ∀ i, Atlas K (Y i)) (w : ∀ i, X → Y i) (s : I → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hdist : ∀ a b, Tendsto (fun i => s i * dist (w i a) (w i b)) (l : Filter I)
      (𝓝 (dist a b))) :
    ∃ B : Atlas K X, ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
      (x : S → X) (U : Tensor K S),
      Tendsto (fun i => s i * (A i).price (fun s => w i (x s)) U)
        (l : Filter I) (𝓝 (B.price x U)) := by
  let P {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (x : S → X) (i : I)
      (U : Tensor K S) := s i * (A i).price (fun s => w i (x s)) U
  obtain ⟨B, hB⟩ := Atlas.of_limit l P (by
    intro S _ _ _ x
    obtain ⟨m, hm⟩ := (Set.finite_range (fun u : S × S => dist (x u.1) (x u.2))).bddAbove
    have h : ∀ᶠ i in (l : Filter I), ∀ a b, s i * dist (w i (x a)) (w i (x b)) ≤ m + 1 := by
      refine eventually_all.mpr fun a => eventually_all.mpr fun b => ?_
      exact (hdist _ _).eventually_le_const ((hm ⟨(a, b), rfl⟩).trans_lt (lt_add_one _))
    refine ⟨(m + 1) * Fintype.card S, h.mono fun i hi => ?_⟩
    obtain ⟨_, d, hd, f, hf, he⟩ := (A i).valid (fun s => w i (x s))
    have hv : P x i ∈ Tensor.ordinary K S (s i * d) :=
      ⟨_, ⟨mul_nonneg (hs i) hd.1, le_rfl⟩, f, hf, funext fun U => by
        simp only [P, he, Tensor.values, mul_assoc]⟩
    have hw (a b) : P x i (Tensor.wire K a b 2) ≤ m + 1 := by
      unfold P
      rw [(A i).wire]
      exact hi _ _
    simpa only [Function.comp_def, Tensor.place_id] using Tensor.ordinary_restrict hv id hw) (by
    intro S _ _ _ x a b
    simp only [P, Atlas.wire]
    exact hdist _ _) (by
    intro S T _ _ _ _ _ _ x y i
    funext U
    exact congrArg (s i * ·) (congrFun ((A i).place (fun s => w i (x s)) y) U))
  exact ⟨B, fun x U => tendsto_pi_nhds.mp (hB x) U⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-!
# Pointed limits of rescaled spectral spaces

Points are represented by bounded sections. The pseudometric keeps
zero-distance representatives distinct. All prices agree on such points.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices
open Spectral Filter Topology

structure Rescale (I : Type*) where
  Y : I → Type
  [metric : ∀ i, MetricSpace (Y i)]
  o : ∀ i, Y i
  d : I → ℝ
  hn : ∀ i, 0 ≤ d i
  l : Ultrafilter I

attribute [instance] Rescale.metric

namespace Rescale
variable {I : Type*} (R : Rescale I)

def Site := {x : ∀ i, R.Y i // ∃ M : ℝ, ∀ᶠ i in (R.l : Filter I), R.d i * dist (x i) (R.o i) ≤ M}

private theorem lim (x y : R.Site) :
    ∃ v : ℝ, Tendsto (fun i => R.d i * dist (x.val i) (y.val i)) (R.l : Filter I) (𝓝 v) := by
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  let f := fun i => R.d i * dist (x.val i) (y.val i)
  have h : ∀ᶠ i in (R.l : Filter I), f i ∈ Set.Icc 0 (a + b) := by
    filter_upwards [ha, hb] with i hx hy
    refine ⟨mul_nonneg (R.hn i) dist_nonneg, ?_⟩
    exact (mul_le_mul_of_nonneg_left (dist_triangle_right _ _ (R.o i)) (R.hn i)).trans
      ((mul_add _ _ _).trans_le (add_le_add hx hy))
  obtain ⟨v, _, hv⟩ := isCompact_Icc.ultrafilter_le_nhds' (R.l.map f) (Filter.mem_map.mpr h)
  exact ⟨v, hv⟩

instance : PseudoMetricSpace R.Site where
  dist x y := (R.lim x y).choose
  dist_self x := tendsto_nhds_unique (R.lim x x).choose_spec (by simp)
  dist_comm x y := tendsto_nhds_unique (R.lim x y).choose_spec
    ((R.lim y x).choose_spec.congr' (Eventually.of_forall (fun i => by rw [dist_comm])))
  dist_triangle x y z := le_of_tendsto_of_tendsto' (R.lim x z).choose_spec
    ((R.lim x y).choose_spec.add (R.lim y z).choose_spec)
    (fun i => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (R.hn i))

theorem distance (x y : R.Site) :
    Tendsto (fun i => R.d i * dist (x.val i) (y.val i)) (R.l : Filter I) (𝓝 (dist x y)) :=
  (R.lim x y).choose_spec

variable (C : ∀ i, Routing.Comparison (R.Y i))

def seg (t : Routing.Fraction) (x y : R.Site) : R.Site := by
  refine ⟨fun i => (C i).seg t (x.val i) (y.val i), ?_⟩
  obtain ⟨a, ha⟩ := x.property
  refine ⟨(dist x y + 1) + a, ?_⟩
  filter_upwards [ha, (R.distance x y).eventually_lt_const
    (lt_add_one (dist x y))] with i hx hxy
  let m := (C i).seg t (x.val i) (y.val i)
  have h : dist m (x.val i) ≤ dist (x.val i) (y.val i) := by
    rw [dist_comm, ((C i).along t _ _).start]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  calc
    R.d i * dist m (R.o i) ≤ R.d i * (dist m (x.val i) + dist (x.val i) (R.o i)) :=
      mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (R.hn i)
    _ ≤ _ := by rw [mul_add]; exact add_le_add ((mul_le_mul_of_nonneg_left h (R.hn i)).trans hxy.le) hx

theorem along (t : Routing.Fraction) (x y : R.Site) : Routing.Along t x y (R.seg C t x y) := by
  intro z
  apply le_of_tendsto_of_tendsto' ((R.distance _ _).pow 2)
    ((((R.distance x z).pow 2).const_mul _ |>.add (((R.distance y z).pow 2).const_mul _)).sub
      (((R.distance x y).pow 2).const_mul _))
  intro i
  change (R.d i * dist ((C i).seg t _ _) _) ^ 2 ≤ _
  linarith only [mul_le_mul_of_nonneg_left ((C i).along t (x.val i) (y.val i) (z.val i))
    (sq_nonneg (R.d i))]

variable {K : Type} [Field K]

theorem atlas (A : ∀ i, Atlas K (R.Y i)) :
    ∃ B : Atlas K R.Site, ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
      (x : S → R.Site) (U : Tensor K S),
      Tendsto (fun i => R.d i * (A i).price (fun s => (x s).val i) U)
        (R.l : Filter I) (𝓝 (B.price x U)) := by
  exact Atlas.scaled_limit R.l R.Y A (fun i (x : R.Site) => x.val i) R.d R.hn R.distance

end Rescale
end OAI.LinearAlgebra.MatrixExponent.Prices
end

/-! # Passing compatible prices to the metric completion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
open Filter Topology
variable {K X Y : Type} [Field K] [PseudoMetricSpace X] [MetricSpace Y]

theorem dense (A : Atlas K X) (f : X → Y) (hf : Isometry f) (hd : DenseRange f) :
    ∃ B : Atlas K Y, ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (x : S → X),
      B.price (f ∘ x) = A.price x := by
  have appr (y : Y) : ∃ t : ℕ → X, Tendsto (fun n => f (t n)) atTop (𝓝 y) := by
    obtain ⟨x, hx, he⟩ := mem_closure_iff_seq_limit.mp (hd y)
    choose t ht using hx
    exact ⟨t, by simpa only [ht] using he⟩
  choose t ht using appr
  let e := Sum.elim f id
  let _ : PseudoMetricSpace (X ⊕ Y) := PseudoMetricSpace.induced e inferInstance
  let w (n : ℕ) := Sum.elim id (fun y => t y n)
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have hw (x : X ⊕ Y) : Tendsto (fun n => f (w n x)) (l : Filter ℕ) (𝓝 (e x)) := by
    cases x with
    | inl x => exact tendsto_const_nhds
    | inr y => exact (ht y).mono_left (Ultrafilter.of_le _)
  obtain ⟨B, hB⟩ := scaled_limit l (fun _ => X) (fun _ => A) w (fun _ => 1)
    (fun _ => zero_le_one) (fun a b => by
      change Tendsto _ _ (𝓝 (dist (e a) (e b)))
      simpa only [one_mul, hf.dist_eq] using (hw a).dist (hw b))
  refine ⟨B.pullback Sum.inr (fun _ _ => rfl), fun _ _ _ _ x => ?_⟩
  change B.price (Sum.inr ∘ f ∘ x) = _
  rw [B.congr (Sum.inr ∘ f ∘ x) (Sum.inl ∘ x) fun i => dist_self (f (x i))]
  funext T
  exact tendsto_nhds_unique (hB (Sum.inl ∘ x) T) (by simp [w])

end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-! # Propagating submean estimates through geodesic constructions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
open Spectral

variable {K S U : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype U] [DecidableEq U] [Nonempty U] {X J : Type*} [PseudoMetricSpace X] [Fintype J]

def Submean (A : Atlas K X) (w : J → ℝ) (x : S → X) (y : J → S → X) : Prop :=
  ∀ B, A.price x B ≤ ∑ j, w j * A.price (y j) B

namespace Submean
variable {A : Atlas K X} {w : J → ℝ} {x : S → X} {y : J → S → X}

theorem reindex (h : A.Submean w x y) (e : U → S) :
    A.Submean w (x ∘ e) (fun j => y j ∘ e) := by
  intro B
  simp only [A.place, Function.comp_apply]
  exact h (Tensor.place e B)

theorem wire (h : A.Submean w x y) (a b : S) :
    dist (x a) (x b) ≤ ∑ j, w j * dist (y j a) (y j b) := by
  simpa only [A.wire] using h (Tensor.wire K a b 2)

theorem extend (h : A.Submean w x y) (hw : ∀ j, 0 ≤ w j)
    (p : U → X) (q : J → U → X)
    (he : ∀ u, ∃ a b : S, ∃ t : ℝ,
      dist (x a) (p u) = t * dist (x a) (x b) ∧
      dist (p u) (x b) = (1 - t) * dist (x a) (x b) ∧
      (∑ j, w j * dist (y j a) (q j u)) ≤ dist (x a) (p u) ∧
      (∑ j, w j * dist (q j u) (y j b)) ≤ dist (p u) (x b)) :
    A.Submean w (Sum.elim x p) (fun j => Sum.elim (y j) (q j)) := by
  let _ := sum_nontrivial S U
  let z := Sum.elim x p
  let v j := Sum.elim (y j) (q j)
  obtain ⟨D, hP⟩ := A.valid z
  let Q (B : Tensor K (S ⊕ U)) := ∑ j, w j * A.price (v j) B
  have hc : Tensor.Cap Q := Tensor.Cap.weighted (fun j =>
    Tensor.cap_ordinary (A.valid (v j)).choose_spec) w hw
  have init (y : S → X) (p : U → X) (B : Tensor K S) :
      A.price (Sum.elim y p) (Tensor.pad U B) = A.price y B := by
    rw [← Tensor.place_inl]
    change (A.price (Sum.elim y p) ∘ Tensor.place Sum.inl) B = _
    rw [← A.place]
    rfl
  have hl (B : Tensor K S) : A.price z (Tensor.place Sum.inl B) ≤ Q (Tensor.pad U B) := by
    simp only [Q, v, z, Tensor.place_inl, init]
    exact h B
  have hh := Tensor.Cap.geodesic_le hP hc Sum.inl Sum.inr hl (fun u => by
    obtain ⟨a, b, t, h₁, h₂, h₃, h₄⟩ := he u
    refine ⟨a, b, t, ?_, ?_, ?_⟩
    · simpa only [Tensor.AtFraction, Tensor.gap, A.wire, z, Sum.elim_inl, Sum.elim_inr]
        using And.intro h₁ h₂
    · simpa only [Tensor.gap, Q, A.wire, z, v, Sum.elim_inl, Sum.elim_inr] using h₃
    · simpa only [Tensor.gap, Q, A.wire, z, v, Sum.elim_inl, Sum.elim_inr] using h₄)
  have id' : Sum.elim Sum.inl Sum.inr = (id : S ⊕ U → S ⊕ U) := by funext i; cases i <;> rfl
  intro B
  simpa only [id', Tensor.place_id] using hh B

end Submean
end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-! Convexity and transport for compatible prices on a pseudometric space. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
open Spectral

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : Atlas K X)
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

theorem chord {x y z : S → X} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h₁ : ∀ i, dist (x i) (z i) = t * dist (x i) (y i))
    (h₂ : ∀ i, dist (z i) (y i) = (1 - t) * dist (x i) (y i)) (T : Tensor K S) :
    A.price z T ≤ (1 - t) * A.price x T + t * A.price y T := by
  let w : Fin 2 → ℝ := ![1 - t, t]
  let v := Sum.elim x y
  let q : Fin 2 → S → X := ![x, y]
  have h : A.Submean w v (fun _ => v) := by
    intro T
    simp [Fin.sum_univ_two, w, sub_mul]
  have h' := h.extend (fun j => by fin_cases j <;> simp [w, ht, ht']) z q (fun i => by
    refine ⟨.inl i, .inr i, t, h₁ i, h₂ i, ?_, ?_⟩ <;> simp [Fin.sum_univ_two, w, q, v, h₁, h₂])
  have he := h'.reindex (Sum.inr : S → (S ⊕ S) ⊕ S) T
  simpa [Fin.sum_univ_two, w, q, Function.comp_def] using he

theorem move_cost (T : Raw K S) (x y : S → X) :
    |A.price x (Tensor.ofRaw T) - A.price y (Tensor.ofRaw T)| ≤
      ∑ i, dist (x i) (y i) * (Real.log (Fintype.card (T.leg i)) / Real.log 2) := by
  let _ := sum_nontrivial S S
  let z := Sum.elim x y
  obtain ⟨D, d, hd, f, hf, he⟩ := A.valid z
  change |A.price (z ∘ Sum.inl) _ - A.price (z ∘ Sum.inr) _| ≤ _
  rw [A.place, A.place, he]
  have hw (i : S) : d * Tensor.dist f (.inl i) (.inr i) = dist (x i) (y i) := by
    have h := A.wire z (.inl i) (.inr i)
    rw [he] at h
    exact h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hT : Tensor.ofRaw T = 0
  · simp only [hT, Function.comp_apply, Tensor.place_zero, sub_self, abs_zero]
    positivity
  have h := Tensor.price_transport f hf T hT Sum.inl Sum.inr
  have h' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hd.1) hl.le
  simp only [Finset.mul_sum, ← mul_assoc, hw, Finset.sum_div, mul_div_assoc] at h'
  simp only [Function.comp_apply, Tensor.values, ← mul_sub, ← sub_div, abs_mul, abs_of_nonneg hd.1,
    abs_div, abs_of_pos hl]
  exact h'

theorem label_move (x y : S → X) : |A.price x 2 - A.price y 2| ≤ ∑ i, dist (x i) (y i) := by
  have h := A.move_cost (Raw.shared K Finset.univ 2) x y
  have hd (i : S) : Fintype.card ((Raw.shared K Finset.univ 2).leg i) = 2 := Fintype.card_fin _
  rw [show Tensor.ofRaw (Raw.shared K Finset.univ 2) = 2 from Tensor.shared_all K 2] at h
  simpa [hd, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] using h

theorem nonnegative (x : S → X) (T : Tensor K S) : 0 ≤ A.price x T := by
  let _ := sum_nontrivial S S
  let v := Sum.elim x x
  obtain ⟨D, d, hd, f, hf, he⟩ := A.valid v
  change 0 ≤ A.price (v ∘ Sum.inl) T
  rw [A.place, he]
  exact Tensor.values_nonneg hd.1 hf _

theorem collapsed (x : S → X) (h : ∀ i j, dist (x i) (x j) = 0) (T : Tensor K S) :
    A.price x T = 0 := by
  let _ := sum_nontrivial S S
  let v := Sum.elim x x
  have hv (i j : S ⊕ S) : dist (v i) (v j) ≤ 0 := by
    cases i <;> cases j <;> exact (h _ _).le
  obtain ⟨d, hd, f, _, he⟩ := A.bounded v hv
  change A.price (v ∘ Sum.inl) T = 0
  rw [A.place, he, show d = 0 by simpa using hd]
  simp [Tensor.values]

end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-!
# Simultaneous finite approximations

Approximate the completed placement by finite models. One common
ultrafilter records all finite lists of sites. Original markings
are included by name, even when two marks coincide in the completion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
open Spectral Filter Topology

variable {K S Y : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
    [MetricSpace Y] {f : Tensor K S →+* ℝ}

theorem approximate (hf : Monotone f) (d : ℝ) (p : Term S → Y) (hd : DenseRange p)
    (he : ∀ (M : TermModel f) (a b), M.Valid a → M.Valid b →
      dist (p a) (p b) = d * Tensor.dist M.g (M.point a) (M.point b)) :
    ∃ (I : Type) (l : Ultrafilter I) (m : I → TermModel f)
      (z : (i : I) → S ⊕ Y → (m i).Site),
      (∀ i a, z i (.inl a) = (m i).point (.mark a)) ∧
      ∀ a b, Tendsto (fun i => d * Tensor.dist (m i).g (z i a) (z i b)) (l : Filter I)
        (𝓝 (dist (Sum.elim (p ∘ Term.mark) id a) (Sum.elim (p ∘ Term.mark) id b))) := by
  classical
  have dense (y : Y) : ∃ t : ℕ → Term S, Tendsto (fun n => p (t n)) atTop (𝓝 y) := by
    obtain ⟨x, hx, he⟩ := mem_closure_iff_seq_limit.mp (hd y)
    choose t ht using hx
    exact ⟨t, by simpa only [ht] using he⟩
  choose t ht using dense
  let I := ℕ × Finset Y
  let l := Ultrafilter.of (atTop : Filter I)
  have hl : (l : Filter I) ≤ atTop := Ultrafilter.of_le _
  have hn : Tendsto (fun i : I => i.1) (l : Filter I) atTop :=
    tendsto_atTop.mpr fun n => hl (eventually_atTop.mpr ⟨(n, ∅), fun _ hi => hi.1⟩)
  let A (i : I) := i.2.image (fun y => t y i.1)
  choose m hm using fun i => exists_model hf (A i)
  let w (i : I) := Sum.elim Term.mark (fun y => t y i.1)
  have valid (a : S ⊕ Y) : ∀ᶠ i in (l : Filter I), (m i).Valid (w i a) := by
    cases a with
    | inl s => exact Eventually.of_forall (fun i => trivial)
    | inr y =>
      apply hl
      refine eventually_atTop.mpr ⟨(0, {y}), fun i hi => ?_⟩
      exact hm i _ (Finset.mem_image.mpr ⟨y, hi.2 (Finset.mem_singleton_self _), rfl⟩)
  have lim (a : S ⊕ Y) : Tendsto (fun i => p (w i a)) (l : Filter I)
      (𝓝 (Sum.elim (p ∘ Term.mark) id a)) := by
    cases a with
    | inl s => exact tendsto_const_nhds
    | inr y => exact (ht y).comp hn
  refine ⟨I, l, m, fun i a => (m i).point (w i a), fun _ _ => rfl, fun a b => ?_⟩
  apply ((lim a).dist (lim b)).congr'
  filter_upwards [valid a, valid b] with i ha hb
  exact he (m i) _ _ ha hb

end OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
end

/-!
# Spectral realization

Assuming squared-distance comparison on finite spectral placements,
complete the geodesic terms generated by the original marking.
Pointwise limits recover compatible ordinary prices for arbitrary
finite placements in the completed space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Filter Topology

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]

variable (K S) in
omit [Nonempty S] in
theorem realize_zero :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (x : S → Y),
      Comparison Y ∧ SpectralSpace K Y ∧ Represents K (0 : Tensor K S → ℝ) x := by
  have eq0 (a b : Unit) : dist a b = 0 := dist_eq_zero.mpr (Subsingleton.elim _ _)
  have H (T : Type) [Fintype T] [DecidableEq T] [Nonempty T] (y : T → Unit)
      (D : ℝ) (hD : 0 < D) : Realized y (0 : Tensor K T → ℝ) D := by
    refine ⟨fun i j => (eq0 _ _).le.trans hD.le, ?_⟩
    intro U _ _ _ z _
    let _ := Prices.Atlas.sum_nontrivial T U
    exact ⟨0, Tensor.zero_ordinary (by positivity), fun _ => rfl, fun _ _ => (eq0 _ _).symm⟩
  refine ⟨Unit, inferInstance, inferInstance, fun _ => (), ?_, ?_, ?_⟩
  · intro a b t _ _
    exact ⟨(), by simp, by simp⟩
  · intro T _ _ _ x
    exact ⟨0, fun _ _ => (eq0 _ _).symm, fun D hD _ => H T x D hD⟩
  · exact ⟨fun _ _ => (eq0 _ _).symm, fun T _ _ _ _ D hD _ => H T _ D hD⟩

theorem realize_atlas (hc : SpectralComparison K) {D : ℝ} {P : Tensor K S → ℝ}
    (hp : P ∈ Tensor.ordinary K S D) :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (x : S → Y),
      Comparison Y ∧ ∃ A : Prices.Atlas K Y, A.price x = P := by
  classical
  obtain ⟨d, ⟨hd, _⟩, f, hf, rfl⟩ := hp
  obtain ⟨Y, _, _, p, C, hp, he⟩ := TermModel.complete hc hf d hd
  obtain ⟨I, l, M, z, hz, hdist⟩ := TermModel.approximate hf d p hp he
  let x := p ∘ Term.mark
  let π := Sum.elim x id
  let _ : PseudoMetricSpace (S ⊕ Y) := PseudoMetricSpace.induced π inferInstance
  let Q {T : Type} [Fintype T] [DecidableEq T] [Nonempty T] (a : T → S ⊕ Y) (i : I) :=
    Tensor.values d (M i).g ∘ Tensor.place (z i ∘ a)
  obtain ⟨A, hl⟩ := Prices.Atlas.of_limit l Q (by
    intro T _ _ _ a
    refine ⟨d * Fintype.card T, Eventually.of_forall fun i => ?_⟩
    have hm : Tensor.values d (M i).g ∈ Tensor.ordinary K (M i).Site d :=
      ⟨d, ⟨hd, le_rfl⟩, (M i).g, (M i).mono, rfl⟩
    refine Tensor.ordinary_restrict hm _ fun j k => ?_
    exact (mul_le_mul_of_nonneg_left (Tensor.dist_le_one _ (M i).mono _ _) hd).trans_eq (mul_one d)) (by
    intro T _ _ _ a j k
    simp only [Q, Function.comp_apply, Tensor.place_wire]
    exact hdist _ _) (by
    intro T U _ _ _ _ _ _ a b i
    funext B
    simp only [Q, Function.comp_apply, ← Tensor.place_comp, Function.comp_assoc])
  refine ⟨Y, inferInstance, inferInstance, x, C, A.pullback Sum.inr (fun _ _ => rfl), ?_⟩
  change A.price (Sum.inr ∘ x) = _
  have eq : A.price (Sum.inr ∘ x) = A.price Sum.inl :=
    A.congr _ _ fun i => dist_self (x i)
  rw [eq]
  apply tendsto_nhds_unique (hl Sum.inl)
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun i => ?_)
  funext B
  have e : z i ∘ Sum.inl = (M i).point ∘ Term.mark := funext (hz i)
  simp only [Q, Function.comp_apply, e, Tensor.values, (M i).initial]

theorem realize (hc : SpectralComparison K) {D : ℝ} {P : Tensor K S → ℝ}
    (hp : P ∈ Tensor.ordinary K S D) :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (x : S → Y),
      Comparison Y ∧ SpectralSpace K Y ∧ Represents K P x := by
  obtain ⟨Y, _, _, x, C, A, rfl⟩ := realize_atlas hc hp
  exact ⟨Y, inferInstance, inferInstance, x, C, A.space, A.represents x⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Finite models for an invariant family of markings

A model for a finite set of group elements realizes all its prices.
Two models containing the support of the same pair of terms agree
on their distance, even after translating the second support.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas

open Routing
open scoped Classical
variable {G K : Type} [Group G] [Field K] [PseudoMetricSpace G]

def Invariant (A : Atlas K G) : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (x : S → G) (g : G),
    A.price (fun i => g * x i) = A.price x

structure Model (A : Atlas K G) (s : Finset G) where
  Site : Type
  [metric : MetricSpace Site]
  cmp : Comparison Site
  B : Atlas K Site
  mark : G → Site
  prices : ∀ {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (x : S → G),
    (∀ i, x i ∈ s) → B.price (mark ∘ x) = A.price x

attribute [instance] Model.metric

theorem exists_model (A : Atlas K G) (s : Finset G) : Nonempty (Model A s) := by
  let T := ↥s ⊕ Bool
  have : Nontrivial T := ⟨Sum.inr false, Sum.inr true, fun e => Bool.false_ne_true (Sum.inr.inj e)⟩
  let z : T → G := Sum.elim Subtype.val (fun _ => 1)
  let y (g : G) : T := if h : g ∈ s then .inl ⟨g, h⟩ else .inr false
  obtain ⟨_, h⟩ := A.valid z
  obtain ⟨Y, _, _, p, C, B, hB⟩ := realize_atlas (spectralComparison K) h
  refine ⟨{ Site := Y, cmp := C, B := B, mark := p ∘ y, prices := ?_ }⟩
  intro S _ _ _ x hx
  rw [Function.comp_assoc, B.place, hB, ← A.place]
  have he : z ∘ y ∘ x = x := by funext i; simp [y, z, hx i]
  rw [he]

namespace Model
variable {A : Atlas K G} {s t : Finset G} (M : Model A s)

def sq (a b : Term G) := dsq (a.eval M.cmp M.mark) (b.eval M.cmp M.mark)

omit [Group G] in
theorem marked {x y : G} (hx : x ∈ s) (hy : y ∈ s) :
    dist (M.mark x) (M.mark y) = dist x y := by
  have h := M.prices ![x, y] (by intro i; fin_cases i <;> assumption)
  simpa only [Atlas.wire, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    using congrFun h (Spectral.Tensor.wire K 0 1 2)

private theorem coord {Y Z S : Type} [MetricSpace Y] [MetricSpace Z]
    [Fintype S] [DecidableEq S] [Nonempty S] {x : S → Y} {y : S → Z} (C : Comparison Y)
    (D : Comparison Z) (P : Atlas K Y) (Q : Atlas K Z)
    (he : P.price x = Q.price y) (a b : Term S) :
    dsq (a.eval C x) (b.eval C x) = dsq (a.eval D y) (b.eval D y) := by
  obtain ⟨B, hB⟩ := (Set.finite_range (fun i : S × S => dist (x i.1) (x i.2))).bddAbove
  have hx i j := hB ⟨(i, j), rfl⟩
  have hy (i j : S) : dist (y i) (y j) ≤ B := by rw [← Q.wire y, ← he, P.wire]; exact hx i j
  apply sub_eq_zero.mp
  apply abs_nonpos_iff.mp
  refine le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
  obtain ⟨_, δ, hδ, h⟩ := finite_terms_tests K {a, b} B hε
  exact h C D (P.realized _ hx) (Q.realized _ hy) (by simp [he, hδ.le]) a (by simp) b (by simp)

def names (a b : Term G) : Finset G := insert 1 (a.support ∪ b.support)

theorem invariant (N : Model A t) (H : A.Invariant) (g : G) (a b : Term G)
    (hs : names a b ⊆ s) (ht : ∀ i ∈ names a b, g * i ∈ t) :
    M.sq a b = N.sq (g • a) (g • b) := by
  let W := names a b
  let _ : Nonempty ↥W := ⟨⟨1, Finset.mem_insert_self _ _⟩⟩
  let lift (i : G) : W := if h : i ∈ W then ⟨i, h⟩ else Classical.arbitrary _
  let x (i : W) := i.val
  let y (i : W) := g * i.val
  have he : M.B.price (M.mark ∘ x) = N.B.price (N.mark ∘ y) := by
    rw [M.prices _ (fun i => hs i.property), N.prices _ (fun i => ht _ i.property)]
    exact (H _ x g).symm
  have ev (u : Term G) (h : u.support ⊆ W) :
      (u.map lift).eval M.cmp (M.mark ∘ x) = u.eval M.cmp M.mark ∧
      (u.map lift).eval N.cmp (N.mark ∘ y) = (g • u).eval N.cmp N.mark := by
    change _ ∧ _ = (u.map (g * ·)).eval _ _
    simp only [Term.eval_map]
    constructor <;> apply Term.eval_congr <;> intro i hi <;> simp [lift, x, y, h hi]
  obtain ⟨ha, ha'⟩ := ev a (fun _ hi => Finset.mem_insert_of_mem (Finset.mem_union_left _ hi))
  obtain ⟨hb, hb'⟩ := ev b (fun _ hi => Finset.mem_insert_of_mem (Finset.mem_union_right _ hi))
  have h := coord M.cmp N.cmp M.B N.B he (a.map lift) (b.map lift)
  rwa [ha, hb, ha', hb'] at h

end Model
end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-!
# Completing an invariant family of marked points

On each pair of formal segments the distance stabilizes as soon as
the finite model contains all their marks. The resulting table gives
an isometric action on a completion. Take simultaneous limits of
prices to retain the marking on this completion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Atlas

open Routing Filter Topology
open scoped Classical
variable {G F : Type} [Group G] [Field F] [PseudoMetricSpace G] {A : Atlas F G}

private theorem table (M : ∀ s, Model A s) (H : A.Invariant) :
    ∃ R : Term G → Term G → ℝ, Table R ∧ (∀ (g : G) a b, R (g • a) (g • b) = R a b) ∧
      ∀ a b, ∀ᶠ s : Finset G in atTop, R a b = (M s).sq a b := by
  let R (a b) := (M (Model.names a b)).sq a b
  have inv (g : G) (a b) : ∀ᶠ s : Finset G in atTop, R a b = (M s).sq (g • a) (g • b) := by
    filter_upwards [eventually_ge_atTop ((Model.names a b).image (g * ·))] with s hs
    exact Model.invariant _ _ H g a b le_rfl fun i hi => hs (Finset.mem_image_of_mem _ hi)
  have he (a b) : ∀ᶠ s : Finset G in atTop, R a b = (M s).sq a b := by simpa using inv 1 a b
  refine ⟨R, ⟨fun _ _ => sq_nonneg _, fun a => ?_, fun a b => ?_, fun a b c => ?_,
    fun t a b c => ?_⟩, fun g a b => ?_, he⟩
  · simp [R, Model.sq, dsq]
  · obtain ⟨s, hs, ht⟩ := ((he a b).and (he b a)).exists
    rw [hs, ht]
    simp only [Model.sq, dsq, dist_comm]
  · obtain ⟨s, h₁, h₂, h₃⟩ := ((he a c).and ((he a b).and (he b c))).exists
    simp only [h₁, h₂, h₃, Model.sq, dsq, Real.sqrt_sq dist_nonneg]
    exact dist_triangle _ _ _
  · obtain ⟨s, h₁, h₂, h₃, h₄⟩ :=
      ((he (.seg t a b) c).and ((he a c).and ((he b c).and (he a b)))).exists
    rw [h₁, h₂, h₃, h₄]
    exact (M s).cmp.along t _ _ _
  · obtain ⟨s, h₁, h₂⟩ := ((he (g • a) (g • b)).and (inv g a b)).exists
    exact h₁.trans h₂.symm

theorem action_hull (A : Atlas F G) (hd : ∀ i j : G, dist i j ≤ 1) (hinv : A.Invariant) :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (_ : MulAction G Y)
      (_ : IsIsometricSMul G Y) (C : Comparison Y) (B : Atlas F Y) (o : Y),
        DenseRange (Term.eval C (fun g : G => g • o)) ∧
        (∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (x : S → G),
          B.price (fun i => x i • o) = A.price x) ∧ ∀ x y : Y, dist x y ≤ 2 := by
  let M := fun s => Classical.choice (A.exists_model s)
  obtain ⟨R, hR, hg, he⟩ := table M hinv
  obtain ⟨Y, _, _, _, _, C, f, hf, hseg, hr, hact⟩ := hR.realize hg
  let _ : PseudoMetricSpace (Term G) := PseudoMetricSpace.induced f inferInstance
  let l := Ultrafilter.of (atTop : Filter (Finset G))
  have hl : (l : Filter (Finset G)) ≤ atTop := Ultrafilter.of_le _
  let u (s : Finset G) := Term.eval (M s).cmp (M s).mark
  obtain ⟨B, hB⟩ := scaled_limit l (fun s => (M s).Site) (fun s => (M s).B) u
    (fun _ => 1) (fun _ => zero_le_one) (fun a b => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hl (he a b)] with s hs
      rw [one_mul]
      exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((hr a b).trans hs))
  obtain ⟨D, hD⟩ := B.dense f (Isometry.of_dist_eq fun _ _ => rfl) hf
  let o := f (.mark 1)
  have ho (i : G) : i • o = f (.mark i) := by
    rw [← hact]
    change f (.mark (i * 1)) = _
    rw [mul_one]
  have eval : Term.eval C (fun g : G => g • o) = f := by
    funext a
    induction a with
    | mark i => exact ho i
    | seg t a b ha hb => rw [Term.eval, ha, hb, hseg]
  have hp (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (x : S → G) :
      D.price (fun i => x i • o) = A.price x := by
    simp only [ho]
    change D.price (f ∘ Term.mark ∘ x) = _
    rw [hD]
    funext T
    refine tendsto_nhds_unique (hB (Term.mark ∘ x) T) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [hl (eventually_ge_atTop (Finset.univ.image x))] with s hs
    rw [one_mul]
    exact congrFun ((M s).prices x (fun i => hs (Finset.mem_image_of_mem x (Finset.mem_univ i)))).symm T
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, C, D, o, eval.symm ▸ hf, hp, ?_⟩
  have near (a : Term G) : dist (f a) o ^ 2 ≤ 1 := by
    induction a with
    | mark g =>
      have h := congrFun (hp _ ![g, 1]) (Spectral.Tensor.wire F 0 1 2)
      simp only [Atlas.wire, Matrix.cons_val_zero, Matrix.cons_val_one, ho] at h
      have hg : dist (f (.mark g)) o ≤ 1 := h.le.trans (hd g 1)
      simpa using pow_le_pow_left₀ dist_nonneg hg 2
    | seg t a b ha hb =>
      rw [hseg]
      have ht := t.2.1
      have ht' := sub_nonneg.mpr t.2.2
      refine ((C.along t (f a) (f b) o).trans (sub_le_self _ (by positivity))).trans ?_
      linarith only [mul_le_mul_of_nonneg_left ha ht', mul_le_mul_of_nonneg_left hb ht]
  have radius (x : Y) : dist x o ≤ 1 := by
    refine hf.induction_on (p := fun y => dist y o ≤ 1) x (isClosed_le (by fun_prop) continuous_const) ?_
    exact fun a => (sq_le_sq₀ dist_nonneg zero_le_one).mp (by simpa using near a)
  exact fun x y => by linarith only [dist_triangle_right x y o, radius x, radius y]

end OAI.LinearAlgebra.MatrixExponent.Prices.Atlas
end

/-!
# Optimizing the sphere price

Transport makes the quadratic objective coercive. One-site controls
therefore apply to actual maximizers. Their increments and the completed
square bound determine the limiting normalized price and widths.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Spectral Filter Finset
open scoped Topology

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]
  {Y : Type*} [MetricSpace Y] {x : A → Y} {P : Tensor F A → ℝ}

omit [DecidableEq A] in
private theorem unit_objective (z : A → F) (n : ℕ) (e : A → ℕ) :
    Budget.value (spherePrice P z) (fun _ => 1) n e = objective P z n e := by
  simp [Budget.value, objective]

theorem saturation_of_controlled (h : Controlled F Y) : Saturation F Y := by
  intro A _ _ _ x o ho z hz
  obtain ⟨P, hP, htest⟩ := h x o ho z hz
  let D := ∑ i, dist o (x i) ^ 2
  have hD : 0 ≤ D := sum_nonneg fun _ _ => sq_nonneg _
  let R := 4 * (D + 1) / entropy ^ 2
  have hR : 0 < R := div_pos (by positivity) (sq_pos_of_pos entropy_pos)
  obtain ⟨C, hc⟩ := htest R hR
  have transport (e : A → ℕ) : spherePrice P z e ≤ ∑ i, dist o (x i) * (1 * width (e i)) := by
    simpa using hP.spherePrice_le z e o
  choose e he using Budget.maximizer transport le_rfl zero_lt_one (fun _ => le_rfl)
    z (hP.spherePrice_nonneg _ _) (fun _ ht => hP.spherePrice_zero ht)
  simp only [unit_objective] at he
  let w (n : ℕ) i := width (e n i) / n
  let B (n : ℕ) := objective P z n (e n)
  have hb (n : ℕ) (hn : 0 < n) (i : A) : w n i ≤ 2 * (D + 1) ∧ (e n i : ℝ) ≤ R * (n : ℝ) ^ 2 := by
    have hh := Budget.bounds transport le_rfl zero_lt_one (fun _ => le_rfl) n hn (e n)
      (by rw [unit_objective]; exact (he n hn).1) i
    simpa only [one_mul] using hh
  have hlim : (∀ i, Tendsto (fun n => w n i) atTop (𝓝 (dist o (x i)))) ∧
      Tendsto (fun n => B n / n) atTop (𝓝 (D / 2)) := by
    apply optimizer_limits (C := C) (by positivity : 0 ≤ 2 * (D + 1))
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact (he n hn).1
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact fun i => ⟨div_nonneg (width_nonneg _) (by positivity), (hb n hn i).1⟩
    · filter_upwards [eventually_gt_atTop 0, hc] with n hn htest
      obtain ⟨_, hne, hm⟩ := he n hn
      obtain ⟨δ, hδ, hδ', hδ''⟩ := htest (e n) hm (fun i => (hb n hn i).2) hne
      refine ⟨δ, hδ, hδ', fun i g hg => ?_⟩
      rw [mul_assoc, ← width]
      unfold w
      rw [div_mul_eq_mul_div]
      exact hδ'' i g hg
    · filter_upwards with n
      simpa only [unit_objective, one_mul] using Budget.squares transport n (e n)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      unfold w B
      have hi := Budget.increment (μ := fun _ => 1) (p := spherePrice P z) (e n) n hn
      simp only [unit_objective, one_mul] at hi
      rw [hi]
      gcongr
      exact (he (n + 1) (by omega)).2.2 _
  refine ⟨P, hP, e, hlim.1, ?_⟩
  have hs : Tendsto (fun n => ∑ i, (w n i) ^ 2) atTop (𝓝 D) :=
    tendsto_finsetSum _ (fun i _ => (hlim.1 i).pow 2)
  have ht := hlim.2.add (hs.div_const 2)
  rw [add_halves] at ht
  apply ht.congr'
  filter_upwards with n
  unfold w B
  have hi := Budget.normalize (μ := fun _ => 1) (p := spherePrice P z) n (e n)
  simp only [unit_objective, one_mul] at hi
  rw [hi, sub_add_cancel]

end OAI.LinearAlgebra.MatrixExponent.Routing
end
