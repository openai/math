import OAI.Hierarchy.ProbeSplit
import OAI.Hierarchy.ProbeTransverse

namespace OAI
/-! # A common Euclidean realization of all lifted columns -/

namespace Hierarchy.AdaptiveProbe
open HyperbolicObstruction LinearAlgebra.SpectralBooks
open scoped BigOperators
noncomputable section

universe u v

abbrev Coordinates (k : ℕ) := EuclideanSpace ℝ (Fin k)

def move {k : ℕ} (x : Coordinates k) (j : Fin k) (t : ℝ) : Coordinates k :=
  WithLp.toLp 2 fun l => x l + if l=j then t else 0

private def tail {k : ℕ} (v : Coordinates (k+1)) : Coordinates k :=
  WithLp.toLp 2 fun j => v j.succ

private def prepend {k : ℕ} (s : ℝ) (v : Coordinates k) : Coordinates (k+1) :=
  WithLp.toLp 2 (Fin.cons s (fun j => v j))

@[simp] private theorem prepend_zero {k : ℕ} (s : ℝ) (v : Coordinates k) : prepend s v 0=s := rfl
@[simp] private theorem tail_prepend {k : ℕ} (s : ℝ) (v : Coordinates k) : tail (prepend s v)=v := by
  ext j
  rfl

private theorem dist_split {k : ℕ} (v w : Coordinates (k+1)) :
    dist v w^2 = (v 0-w 0)^2+dist (tail v) (tail w)^2 := by
  rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_succ,EuclideanSpace.dist_sq_eq]
  simp only [Real.dist_eq,sq_abs]
  rfl

private theorem tail_move_zero {k : ℕ} (s : ℝ) (v : Coordinates k) (t : ℝ) :
    tail (move (prepend s v) 0 t)=v := by
  ext j
  change v j + (if j.succ=0 then t else 0) = v j
  simp only [ite_eq_right (Fin.succ_ne_zero j),add_zero]

private theorem tail_move_succ {k : ℕ} (s : ℝ) (v : Coordinates k) (j : Fin k) (t : ℝ) :
    tail (move (prepend s v) j.succ t) = move v j t := by
  ext l
  change v l + (if l.succ=j.succ then t else 0) = v l+(if l=j then t else 0)
  simp only [Fin.succ_inj]

structure MarkedProduct {I : Type v} {X : Type u} [MetricSpace X] {k : ℕ} (A : Axes I X k) where
  fiber : Type u
  [metric : MetricSpace fiber]
  cat : CATZero fiber
  embed : Coordinates k → fiber → X
  coordinate : I → Coordinates k
  mark : I → fiber
  product : ∀ x y p q, dist (embed x p) (embed y q)^2 = dist x y^2 + dist p q^2
  center : ∀ i, embed (coordinate i) (mark i)=A.center i
  axis : ∀ i j t, embed (move (coordinate i) j t) (mark i)=A.axis i j t

attribute [instance] MarkedProduct.metric

/-- Splitting one axis leaves another system of the same kind on the
transverse factor. The full parameterized axes are carried at each split. -/
theorem marked_product {I : Type v} (base : I) (k : ℕ) {X : Type u} [MetricSpace X]
    (C : CATZero X) (A : Axes I X k) : Nonempty (MarkedProduct A) := by
  induction k generalizing X with
  | zero =>
    exact ⟨{
      fiber := X
      cat := C
      embed := fun _ p => p
      coordinate := fun _ => 0
      mark := A.center
      product := fun x y p q => by simp [Subsingleton.elim x y]
      center := fun _ => rfl
      axis := fun _ j => Fin.elim0 j
    }⟩
  | succ k ih =>
    obtain ⟨Y,metric,cat,rest,phase,e,pyth,first,other⟩ := split_axis C base A
    obtain ⟨P⟩ := ih cat rest
    refine ⟨{
      fiber := P.fiber
      cat := P.cat
      embed := fun s p => e (s 0) (P.embed (tail s) p)
      coordinate := fun i => prepend (phase i) (P.coordinate i)
      mark := P.mark
      product := ?_
      center := ?_
      axis := ?_
    }⟩
    · intro x y p q
      rw [pyth,P.product,dist_split x y]
      ring
    · intro i
      simp only [prepend_zero,tail_prepend,P.center]
      simpa only [add_zero,A.starts] using first i 0
    · intro i j
      refine Fin.cases ?_ (fun l => ?_) j
      · intro t
        rw [tail_move_zero,P.center]
        change e (phase i+(if (0 : Fin (k+1))=0 then t else 0)) _ = _
        simpa using first i t
      · intro t
        rw [tail_move_succ,P.axis]
        change e (phase i+(if (0 : Fin (k+1))=l.succ then t else 0)) _ = _
        simpa only [ite_eq_right (Fin.succ_ne_zero l).symm,add_zero] using other i l t

/-- At maximal flat dimension the transverse marks coincide. Every tile
and every one of its signed axis readings now uses the same coordinates. -/
theorem exact_column_coordinates {F : Type*} [Field F] {I : Type v} (base : I)
    {k : ℕ} {X : Type} [MetricSpace X] (prices : SpectralPlacementPrices F X)
    (C : CATZero X) (no : ¬ HasSpectralFlat F (k+1)) (A : Axes I X k) :
    ∃ z : I → Coordinates k, (∀ i i', dist (A.center i) (A.center i') = dist (z i) (z i')) ∧
      ∀ i i' j t, dist (A.center i) (A.axis i' j t) = dist (z i) (move (z i') j t) := by
  obtain ⟨P⟩ := marked_product base k C A
  let : Subsingleton P.fiber := transverse_subsingleton prices C no P.embed P.product
  refine ⟨P.coordinate, ?_, ?_⟩
  · intro i i'
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [←P.center i,←P.center i',P.product,Subsingleton.elim (P.mark i) (P.mark i'),dist_self]
    ring
  · intro i i' j t
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [←P.center i,←P.axis i' j t,P.product,Subsingleton.elim (P.mark i) (P.mark i'),dist_self]
    ring

end
end Hierarchy.AdaptiveProbe

end OAI
