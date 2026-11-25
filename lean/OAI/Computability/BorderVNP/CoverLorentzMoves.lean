import OAI.Computability.BorderVNP.CoverLorentzProduct
import OAI.Computability.BorderVNP.CoverSiteRounding
import OAI.Computability.BorderVNP.CoverDeckProductRoute

/-!
# Allowed site moves in the actual product cover

A site has one congruence address in each surface factor. All nonidentity site
moves with displacement at most a fixed constant form a finite set, independent
of the level. The constant can be chosen to include both routing generators and
all outcomes of rounding a sufficiently short segment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open UpperHalfPlane Set Matrix BorderVNP.Epoch

variable {I : Type*} [Fintype I]

/-- The base site in the product universal cover. -/
def productOrigin (I : Type*) : HyperbolicHost I := WithLp.toLp 2 (fun _ => UpperHalfPlane.I)

/-- An integral site translation moves every coordinate by its own quaternion. -/
noncomputable def translatePoint (s : I → gamma 1) (x : HyperbolicHost I) : HyperbolicHost I :=
  WithLp.toLp 2 (fun i => gammaSL 1 (s i) • x i)

/-- The distance between product points is invariant under the integral translation. -/
theorem translatePoint_isometry (s : I → gamma 1) : Isometry (translatePoint s) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, host_dist_sq,host_dist_sq]
  exact Finset.sum_congr rfl (fun i _ => congrArg (·^2) (dist_smul (gammaSL 1 (s i)) (x i) (y i)))

/-- Displacement of a site move upstairs, before passing to any particular quotient. -/
noncomputable def moveLength (s : I → gamma 1) : ℝ :=
  dist (productOrigin I) (translatePoint s (productOrigin I))

/-- Freeness identifies exactly the moves of positive length. -/
theorem moveLength_pos {s : I → gamma 1} : 0 < moveLength s ↔ s ≠ 1 := by
  rw [moveLength,dist_pos]
  constructor
  · intro h he
    apply h
    subst s
    apply PiLp.ext
    intro i
    change UpperHalfPlane.I = gammaSL 1 1 • UpperHalfPlane.I
    simp
  · intro h he
    apply h
    funext i
    exact eq_one_of_fix (s i) UpperHalfPlane.I (congrArg (fun x : HyperbolicHost I => x i) he.symm)

private theorem finite_choices {G : Type*} {s : Set G} (h : s.Finite) :
    (Set.pi univ (fun _ : I => s)).Finite := by
  classical
  have := h.fintype
  apply (finite_range (fun a : I → s => fun i => (a i).val)).subset
  intro a ha
  exact ⟨fun i => ⟨a i,ha i (mem_univ i)⟩,rfl⟩

/-- All bounded-displacement integral product moves form a finite catalog. -/
theorem finite_bounded_moves (L : ℝ) : {s : I → gamma 1 | moveLength s ≤ L}.Finite := by
  have h := finite_sites 1 (ProperSpace.isCompact_closedBall UpperHalfPlane.I L)
  apply (finite_choices (I := I) h).subset
  intro s hs i _
  change dist (gammaSL 1 (s i) • UpperHalfPlane.I) UpperHalfPlane.I ≤ L
  rw [dist_comm]
  exact (PiLp.dist_apply_le (productOrigin I) (translatePoint s (productOrigin I)) i).trans hs

/-- Positive-length allowed moves at a prescribed displacement budget. -/
noncomputable def allowedMoves (I : Type*) [Fintype I] (L : ℝ) : Finset (I → gamma 1) := by
  classical
  exact (finite_bounded_moves (I := I) L).toFinset.erase 1

/-- The catalog admits every nontrivial displacement up to and including its budget. -/
theorem mem_allowedMoves {L : ℝ} {s : I → gamma 1} :
    s ∈ allowedMoves I L ↔ s ≠ 1 ∧ moveLength s ≤ L := by
  classical
  rw [allowedMoves,Finset.mem_erase,(finite_bounded_moves _).mem_toFinset]; rfl

/-- Rounding each factor produces the product tile address of an endpoint. -/
noncomputable def productAddress (d : ℕ) (x : SurfaceHost I (d+1)) : I → Deck (d+1) :=
  fun i => surfaceAddress d (x i)

/-- Reduction of an integral product move to any cover level. -/
def reduceMove (d : ℕ) (s : I → gamma 1) : I → Deck (d+1) := fun i => (s i : Deck (d+1))

/-- At one level-independent budget, all routing generators and all nonlocal outcomes of
rounding a segment of length at most `h` belong to the same allowed-move catalog. -/
theorem exists_move_budget (h : ℝ) : ∃ L : ℝ, 0 < L ∧
    (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) →
      s ∈ allowedMoves I L) ∧
    ∀ d (x y : SurfaceHost I (d+1)), dist x y ≤ h → productAddress d x ≠ productAddress d y →
      ∃ s ∈ allowedMoves I L, productAddress d y = productAddress d x * reduceMove d s := by
  classical
  obtain ⟨_,M,_,_,hM⟩ := finite_rounding_moves h
  let G := {u : gamma 1 | u = 1 ∨ u.val ∈ routingGenerators}
  have hG : G.Finite := (Set.finite_singleton 1).union
    (routingGenerators.finite_toSet.preimage Subtype.val_injective.injOn)
  let T := Set.pi univ (fun _ : I => G ∪ (M : Set (gamma 1)))
  have hT : T.Finite := finite_choices (I := I) (hG.union M.finite_toSet)
  obtain ⟨b,hb⟩ := (hT.image (moveLength (I := I))).bddAbove
  let L := max b 0 + 1
  have bound (s : I → gamma 1) (hs : s ∈ T) : moveLength s ≤ L :=
    (hb ⟨s,hs,rfl⟩).trans ((le_max_left b 0).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨L,by dsimp [L]; positivity,?_,?_⟩
  · intro s hs hg
    exact mem_allowedMoves.mpr ⟨hs,bound _ (fun i _ => Or.inl (hg i))⟩
  · intro d x y hxy hne
    choose s hs he using (fun i => hM d (x i) (y i) ((PiLp.dist_apply_le x y i).trans hxy))
    have heq : productAddress d y = productAddress d x * reduceMove d s := funext he
    have hn : s ≠ 1 := by
      intro h
      apply hne
      rw [heq,h]
      funext i
      change surfaceAddress d (x i) = surfaceAddress d (x i) * ((1 : gamma 1) : Deck (d+1))
      simp
    exact ⟨s,mem_allowedMoves.mpr ⟨hn,bound _ (fun i _ => Or.inr (hs i))⟩,heq⟩

/-- Uniformly at every sufficiently deep level, the product site wire has exactly its
catalogued length, whatever its initial address. -/
theorem eventually_move_length (L : ℝ) : ∃ l, ∀ d ≥ l, ∀ a : I → gamma 1,
    ∀ s ∈ allowedMoves I L,
      dist (productProjection d (translatePoint a (productOrigin I)))
        (productProjection d (translatePoint a (translatePoint s (productOrigin I)))) = moveLength s := by
  obtain ⟨l,hl⟩ := eventually_productProjection_isometry (I := I) L
  refine ⟨l,?_⟩
  intro d hd a s hs
  let x := translatePoint a (productOrigin I)
  let y := translatePoint a (translatePoint s (productOrigin I))
  have hlen : dist x y = moveLength s := (translatePoint_isometry a).dist_eq _ _
  have hL : 0 ≤ L := (dist_nonneg.trans hlen.le).trans (mem_allowedMoves.mp hs).2
  have hy : y ∈ Metric.closedBall x L := by rw [Metric.mem_closedBall,dist_comm,hlen]; exact (mem_allowedMoves.mp hs).2
  exact ((hl d hd x).dist_eq ⟨x,Metric.mem_closedBall_self hL⟩ ⟨y,hy⟩).trans hlen

end Cover

end BorderVNP
end Computability
end OAI
