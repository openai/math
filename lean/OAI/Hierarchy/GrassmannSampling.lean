import OAI.Hierarchy.GrassmannSamplingPairs
import OAI.Hierarchy.GrassmannCube
import OAI.Hierarchy.MatchedFiberKernel

namespace OAI
/-! # Grassmann mean bounds on random linear observations

For complementary planes the sampled labels are independent. For adjacent
planes the common intersection label selects a fiber, and the two remaining
labels are independent within their respective fibers.
-/

noncomputable section
namespace Hierarchy.NonlinearExpanders.GrassmannSampling

open ThreeFlat.Expander Computability.VPVNP.Grassmann
open Hierarchy.GrassmannCube Finset

universe u

theorem complementary_nonempty (m : ℕ) : Nonempty (Pair m m) := by
  let v : Fin m → Bool := fun _ => false
  let w : Fin m → Bool := fun _ => true
  have ht := plane_pair v w
  have h : hamming v w = m := by simp [hamming,v,w]
  rw [h] at ht
  exact ⟨⟨(plane v, plane w), ht⟩⟩

theorem adjacent_nonempty {m : ℕ} (hm : 0 < m) : Nonempty (Pair m 1) := by
  let j : Fin m := ⟨0,hm⟩
  let v : Fin m → Bool := fun _ => false
  let w : Fin m → Bool := fun i => decide (i=j)
  have ht := plane_pair v w
  have hfilter : (univ.filter fun i => v i ≠ w i) = {j} := by
    ext i
    by_cases hi : i = j <;> simp [v,w,hi]
  have h : hamming v w = 1 := by simp [hamming,hfilter]
  exact ⟨⟨(plane v, plane w),h ▸ ht⟩⟩

private theorem avg_singleFiber {A T : Type*} [Fintype A] [Subsingleton T]
    (e : A ≃ A × T) (t : T) (F : A → ℝ) :
    (avg fun a => F (e.symm (a,t))) = avg F := by
  let f : A ≃ A := {
    toFun a := e.symm (a,t)
    invFun x := (e x).1
    left_inv a := by simp
    right_inv x := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl (Subsingleton.elim _ _) }
  exact avg_equiv f F

private theorem complementary_expectation {m n : ℕ} (p : Pair m m) {X : Type*} [PseudoMetricSpace X]
    (x : Label n m → X) : (avg fun g : Read n (Space m) =>
      dist (x (observe p.val.1 g)) (x (observe p.val.2 g))^2) = variance x := by
  let delta (a b : Label n m) := dist (x a) (x b)^2
  change (avg fun g : Read n (Space m) => delta (observe p.val.1 g) (observe p.val.2 g)) = _
  rw [pair_expectation]
  let : Subsingleton (Label n (m-m)) := by simp only [Label, Nat.sub_self, pow_zero]; infer_instance
  let : Nonempty (Label n (m-m)) := by simp only [Label, Nat.sub_self, pow_zero]; infer_instance
  calc
    _ = avg (fun _ : Label n (m-m) => variance x) := by
      apply avg_congr
      intro t
      calc
        _ = avg (fun a => avg (delta ((layoutLeft n p).symm (a,t)))) :=
          avg_congr _ _ fun a => avg_singleFiber (layoutRight n p) t _
        _ = variance x := avg_singleFiber (layoutLeft n p) t (fun a => avg (delta a))
    _ = _ := avg_const _

private theorem layouts {m n : ℕ} (hm : 0 < m) :
    ∃ e f : Pair m 1 → Label n m ≃ Label n 1 × Label n (m-1),
      ∀ (X : Type u) [PseudoMetricSpace X] (β : ℝ),
      (∀ y : Plane m → X, mean (fun U V => dist (y U) (y V)^2) m ≤
        β * mean (fun U V => dist (y U) (y V)^2) 1) →
      ∀ x : Label n m → X, variance x ≤ β * pairedEnergy e f x := by
  let := complementary_nonempty m
  let := adjacent_nonempty hm
  refine ⟨layoutLeft n,layoutRight n,?_⟩
  intro X _ β gap x
  let D (g : Read n (Space m)) (U V : Plane m) := dist (x (observe U g)) (x (observe V g))^2
  have mean_eq (r : ℕ) : (avg fun g => mean (D g) r) =
      avg (fun p : Pair m r => avg fun g => D g p.val.1 p.val.2) :=
    avg_comm (fun g (p : Pair m r) => D g p.val.1 p.val.2)
  have comp : (avg fun g => mean (D g) m) = variance x := by
    rw [mean_eq]
    calc
      _ = avg (fun _ : Pair m m => variance x) :=
        avg_congr _ _ fun p => complementary_expectation p x
      _ = _ := avg_const _
  have adj : (avg fun g => mean (D g) 1) = pairedEnergy (layoutLeft (r := 1) n) (layoutRight n) x := by
    rw [mean_eq]
    exact avg_congr _ _ fun p => pair_expectation p (fun a b => dist (x a) (x b)^2)
  have h : (avg fun g => mean (D g) m) ≤ avg (fun g => β * mean (D g) 1) :=
    avg_le fun g => gap (fun U => x (observe U g))
  rwa [avg_mul,comp,adj] at h

/-- The layouts depend only on the binary vector-space dimensions. They work
at every target and every Poincaré constant satisfying the Grassmann mean
inequality. -/
theorem exists_paired_layouts (m n : ℕ) (hm : 0 < m) :
    ∃ e f : Pair m 1 → Fin ((2^n)^m) ≃ Fin (2^n) × Fin ((2^n)^(m-1)),
      ∀ (X : Type u) [PseudoMetricSpace X] (β : ℝ),
      (∀ y : Plane m → X, mean (fun U V => dist (y U) (y V)^2) m ≤
        β * mean (fun U V => dist (y U) (y V)^2) 1) →
      ∀ x : Fin ((2^n)^m) → X, variance x ≤ β * pairedEnergy e f x := by
  let family (b : ℕ) : Prop :=
    ∃ e f : Pair m 1 → Fin ((2^n)^m) ≃ Fin b × Fin ((2^n)^(m-1)),
      ∀ (X : Type u) [PseudoMetricSpace X] (β : ℝ),
      (∀ y : Plane m → X, mean (fun U V => dist (y U) (y V)^2) m ≤
        β * mean (fun U V => dist (y U) (y V)^2) 1) →
      ∀ x : Fin ((2^n)^m) → X, variance x ≤ β * pairedEnergy e f x
  have h : family ((2^n)^1) := layouts.{u} (n := n) hm
  exact Eq.mp (congrArg family (pow_one (2^n : ℕ))) h

end Hierarchy.NonlinearExpanders.GrassmannSampling

end
end OAI
