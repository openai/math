import OAI.Hierarchy.Flat
import OAI.Hierarchy.CubeExclusion
import OAI.ThreeFlat.PortExtension

namespace OAI
/-! # The nonlinear expander input in unbounded flat dimension

The geometric hypothesis is a uniform distortion gap on one fixed finite
cube in every member of the class of targets. The coefficient field enters
only when supplying that class and verifying the hypothesis. -/

namespace Hierarchy.NonlinearExpanders

open LinearAlgebra.SpectralBooks ThreeFlat.Expander
open HyperbolicObstruction
open scoped BigOperators

/-- The integer multiplicities of a connected loopless undirected regular
multigraph on exactly 2^n labelled vertices. -/
structure Graph (n h : ℕ) where
  arcs : Fin (2^n) → Fin (2^n) → ℕ
  symmetric : ∀ i j, arcs i j = arcs j i
  loopless : ∀ i, arcs i i = 0
  regular : ∀ i, ∑ j, arcs i j = h
  connected : ∀ i j, Relation.ReflTransGen (fun a b => 0 < arcs a b) i j

/-- The arbitrary-dimensional nonlinear expander theorem used in the paper
(VP, Section 15), stated independently of spectral prices or arithmetic circuits.
The Poincaré constant and degree are common to the entire target family. -/
def ExcludedCubeTheorem : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ε : ℝ), 0 < ε →
    ∀ (I : Type 1) (X : I → Type) [_me : ∀ i, MetricSpace (X i)]
      [_cm : ∀ i, CompleteSpace (X i)], (∀ i, CATZero (X i)) →
      (∀ i (x : CubeExclusion.Vertex d → X i) (r : ℝ), 0 < r →
        ∃ a b, ε ≤ |r * dist (x a) (x b) - dist (CubeExclusion.corner a) (CubeExclusion.corner b)|) →
      ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧
        ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ G : Graph n h, ∀ i, Bound (transition G.arcs h) (X i) γ

/-- A field-specific family, including the scalar target for the clipping/cut proof. -/
def SpectralFamily (F : Type*) [Field F] : Prop :=
  ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧ ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ G : Graph n h,
    Bound (transition G.arcs h) ℝ γ ∧ ∀ (X : Type) [MetricSpace X] [CompleteSpace X],
      SpectralPlacementPrices F X → CATZero X → Bound (transition G.arcs h) X γ

private structure Target (F : Type*) [Field F] where
  carrier : Type
  [metric : MetricSpace carrier]
  [complete : CompleteSpace carrier]
  prices : SpectralPlacementPrices F carrier
  cat : CATZero carrier

attribute [instance] Target.metric Target.complete

/-- The real line belongs to the same spectral family, by an axis in the
field's spectral plane. No separate Euclidean expander sequence is required. -/
theorem family_of_missing (expanders : ExcludedCubeTheorem) {F : Type} [Field F]
    {d : ℕ} (large : 2 ≤ d) (missing : ¬HasSpectralFlat F d) : SpectralFamily F := by
  obtain ⟨ε, pos, gap⟩ := CubeExclusion.uniform_gap missing
  let carrier := fun t : Target F => t.carrier
  obtain ⟨h, γ, hh, hγ, graphs⟩ := expanders d large ε pos (Target F) carrier
    (fun t => t.cat) (fun t => gap t.carrier t.prices t.cat)
  obtain ⟨P⟩ := HasSpectralFlat.plane F
  let e : ℝ → EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2)
  have he : Isometry e := Isometry.of_dist_eq (PiLp.dist_single_same 2 (fun _ : Fin 2 => ℝ) 0)
  let line : Target F := ⟨ℝ, P.pullback e he, innerProductSpace_catZero ℝ⟩
  refine ⟨h,γ,hh,hγ,fun n₀ => ?_⟩
  obtain ⟨n,hn,G,all⟩ := graphs n₀
  refine ⟨n,hn,G,all line,?_⟩
  intro X met complete Q cat
  exact all ⟨X, Q, cat⟩

/-- In every finite spectral placement, bounded incident demands have at most
a fixed multiple of the supply's aggregate wire length. This is the metric
half of the integral port restriction, with constants independent of graph order. -/
theorem demand_bounds {F : Type*} [Field F] (family : SpectralFamily F) :
    ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧ ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ G : Graph n h,
      ∀ (X : Type) [MetricSpace X], SpectralPlacementPrices F X →
      ∀ (x : Fin (2^n) → X) (w : Fin (2^n) → Fin (2^n) → ℝ) (W : ℝ), 0 ≤ W →
      (∀ i j, 0 ≤ w i j) → (∀ i, ∑ j, w i j ≤ W) → (∀ j, ∑ i, w i j ≤ W) →
      ∑ i, ∑ j, w i j * dist (x i) (x j) ≤
        (40 * W * γ / h) * ∑ e : Arc G.arcs, dist (x (arcStart e)) (x (arcEnd e)) := by
  obtain ⟨h,γ,hh,hγ,graphs⟩ := family
  refine ⟨h,γ,hh,hγ,fun n₀ => ?_⟩
  obtain ⟨n,hn,G,scalar,metric⟩ := graphs n₀
  exact ⟨n,hn,G,fun _ _ P x w _ hW =>
    port_demand_bound_of_spectral_extension P hh hγ hW scalar metric x w⟩

end Hierarchy.NonlinearExpanders

end OAI
