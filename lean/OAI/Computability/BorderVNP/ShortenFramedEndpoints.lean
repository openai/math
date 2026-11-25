import OAI.Computability.BorderVNP.ShortenFramedPlacement
import OAI.Computability.BorderVNP.ShortenCanonicalPlacement

/-!
# Signed slots and true quotient lengths for sampled packs

The measured direction bin uses `true` for the negative end of the geodesic.
After decoding its tile shift and relative direction, both resulting points
are exactly the old slots moved by the whole-pack sample. On sufficiently
deep surfaces the common short length is preserved exactly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Framed

open Cover BorderVNP.Cover.Frame Epoch Crossing Hecke Set
open scoped Classical

variable {D d n : ℕ} {I : Type*} [Fintype I]

omit [Fintype I] in
private theorem productLine_neg (v : PiLp 2 (fun _ : I => ℂ)) (t : ℝ) :
    productLine (-v) t = productLine v (-t) := by
  ext1 i
  change tangentLine (unitDirection (-(v i))) (t * ‖-(v i)‖) =
    tangentLine (unitDirection (v i)) ((-t)*‖v i‖)
  by_cases h : v i = 0
  · simp [h,tangentLine]
  · simp [tangentLine,unitDirection,h,neg_mul,smul_neg,neg_smul]

/-- Projection at the specified absolute output tile. -/
noncomputable def tileProject (t : I → Deck d) (x : HyperbolicHost I) : SurfaceHost I d :=
  productProjection d (translatePoint (deckRep t) x)

/-- Installing a lifted pattern cannot increase distances in the quotient. -/
theorem tileProject_nonexpanding (t : I → Deck d) (x y : HyperbolicHost I) :
    dist (tileProject t x) (tileProject t y) ≤ dist x y :=
  (productProjection_dist_le _ _ _).trans_eq ((translatePoint_isometry _).dist_eq _ _)

/-- The data supplied to the canonical placement construction for a moved cable. -/
noncomputable def record {S : Type} (s : Catalog.SegmentType (Cube D)) (kind : S)
    (b : Cube D → gamma 1) (sample : PackSample (lattice 1) elliptic (Cube D) d n) :
    CanonicalPlacement.Segment (Cube D → Deck d) S (relativeWindow (Cube D)) where
  tile := shiftedAddress sample.2.2 (movedCarry s b sample.1 sample.2.1)
  kind := kind
  center := (configuration s b sample.1 sample.2.1).1
  direction := (configuration s b sample.1 sample.2.1).2
  mem := configuration_center s b sample.1 sample.2.1
  norm := configuration_unit s b sample.1 sample.2.1

/-- The point read from either signed slot of the sampled segment is exactly
the point obtained by moving its corresponding input endpoint. -/
theorem projects {S : Type} (s : Catalog.SegmentType (Cube D)) (kind : S)
    (b : Cube D → gamma 1) (sample : PackSample (lattice 1) elliptic (Cube D) d n) (neg : Bool) :
    let y := record s kind b sample
    tileProject y.tile (endpoint y.center y.direction s.radius neg) =
      sampleMove sample (productProjection _ (translatePoint b (if neg then s.ends.1 else s.ends.2))) := by
  intro y
  cases neg with
  | false => exact (projects_line s b sample s.radius).symm
  | true =>
    change tileProject y.tile (shiftTo y.center (productLine (-y.direction) s.radius)) = _
    rw [productLine_neg]
    exact (projects_line s b sample (-s.radius)).symm

/-- On deep levels the actual distance between the moved quotient endpoints equals
the length measured in the lifted segment catalog, uniformly in every listed motion. -/
theorem eventually_length (R : ℝ) (hR : 0 ≤ R) :
    ∃ l, ∀ d ≥ l, ∀ n (s : Catalog.SegmentType I) (b : I → gamma 1)
      (sample : PackSample (lattice 1) elliptic I d n), 2*s.radius ≤ R →
      dist (sampleMove sample (productProjection _ (translatePoint b s.ends.1)))
        (sampleMove sample (productProjection _ (translatePoint b s.ends.2))) = 2*s.radius := by
  obtain ⟨l,hl⟩ := eventually_productProjection_isometry (I := I) R
  refine ⟨l,?_⟩
  intro d hd n s b sample hr
  let c := configuration s b sample.1 sample.2.1
  let a := deckRep (shiftedAddress sample.2.2 (movedCarry s b sample.1 sample.2.1))
  let pos (t : ℝ) := translatePoint a (shiftTo c.1 (productLine c.2 t))
  have hdist : dist (pos (-s.radius)) (pos s.radius) = 2*s.radius := by
    rw [show dist (pos (-s.radius)) (pos s.radius) =
      dist (productLine c.2 (-s.radius)) (productLine c.2 s.radius) by
        unfold pos; rw [(translatePoint_isometry a).dist_eq,(shiftTo_isometry c.1).dist_eq]]
    rw [dist_productLine,configuration_unit,mul_one,show -s.radius-s.radius = -(2*s.radius) by ring,
      abs_neg,abs_of_nonneg (by linarith [s.positive])]
  have hnear : pos s.radius ∈ Metric.closedBall (pos (-s.radius)) R := by
    change dist (pos s.radius) (pos (-s.radius)) ≤ R
    rw [dist_comm,hdist]; exact hr
  have hs := (hl d hd (pos (-s.radius))).dist_eq
    ⟨pos (-s.radius),Metric.mem_closedBall_self hR⟩ ⟨pos s.radius,hnear⟩
  change dist (productProjection d (pos (-s.radius))) (productProjection d (pos s.radius)) =
    dist (pos (-s.radius)) (pos s.radius) at hs
  change dist (sampleMove sample (productProjection _ (translatePoint b (shiftTo s.center (productLine s.direction (-s.radius))))))
    (sampleMove sample (productProjection _ (translatePoint b (shiftTo s.center (productLine s.direction s.radius))))) = _
  rw [projects_line,projects_line]
  exact hs.trans hdist

/-- Public numbering of the finite Hecke candidate list, prepared independently of the seed charts. -/
noncomputable def sampleNames (I : Type*) [Fintype I] (n : ℕ) :
    (Equiv.Perm I × ProductSample (lattice 1) elliptic I n) ≃
      Fin (Fintype.card (Equiv.Perm I × ProductSample (lattice 1) elliptic I n)) :=
  Fintype.equivFin _

/-- A finite catalog of moves used by the iteration depends only on the word cutoff
and the seed table, independently of the level at which the moves are applied. -/
noncomputable def samplePattern (I : Type*) [Fintype I] (D n bins : ℕ) (chart : Fin bins → SeedChart I D) :
    Catalog.Pattern I D := by
  classical
  let M := Equiv.Perm I × ProductSample (lattice 1) elliptic I n
  let e := sampleNames I n
  exact
    { moves := Fintype.card M
      depth := n
      perm := fun m => (e.symm m).1
      matrix := fun m => wordMatrix (e.symm m).2
      clears := fun m => wordMatrix_clears (e.symm m).2
      bins := bins
      chart := chart }

/-- Identify the catalog entry for the chosen permutation and words, leaving the
variable final deck translation outside the finite pattern. -/
theorem samplePattern_move (D bins : ℕ) (chart : Fin bins → SeedChart I D)
    (s : PackSample (lattice 1) elliptic I d n) :
    ∃ j : Fin (samplePattern I D n bins chart).moves, ∀ x : HyperbolicHost I,
      sampleMove s (productProjection _ x) = productProjection d
        (translatePoint (deckRep s.2.2) (Catalog.motion ((samplePattern I D n bins chart).perm j)
          ((samplePattern I D n bins chart).matrix j) x)) := by
  let e := sampleNames I n
  refine ⟨e (s.1,s.2.1),?_⟩
  intro x
  simp only [samplePattern,e,Equiv.symm_apply_apply]
  exact sampleMove_projection s x

end Shortening.Framed

end BorderVNP
end Computability
end OAI
