import OAI.Computability.BorderVNP.ShortenEpochFramedSegments
import OAI.Computability.BorderVNP.ShortenCatalogBounds
import OAI.Computability.BorderVNP.CoverPackBins
import OAI.Computability.BorderVNP.ShortenCanonicalChart

/-!
# A common pack motion acts on actual framed segment endpoints

A catalogued oriented cable has one midpoint frame in each factor, chosen
from its tangent direction, and one lift of its tile name. A pack sample
permutes the factors, applies the sampled Hecke words and then translates
by the sampled deck name. The geometry uses the same quotient frames and
relative chart as the bin probabilities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Framed

open Cover BorderVNP.Cover.Frame Epoch Hecke Set UpperHalfPlane
open scoped Classical Matrix

variable {I : Type*} [Fintype I] {n d : ℕ}

/-- The component speeds of an oriented segment type. -/
noncomputable def speed (s : Catalog.SegmentType I) (i : I) : ℝ := ‖s.direction i‖

/-- The actual pre-motion frame for the endpoint chart, including its input tile lift. -/
noncomputable def sourceFrame (s : Catalog.SegmentType I) (b : I → gamma 1) (p : Equiv.Perm I) (i : I) : SL :=
  gammaSL 1 (b (p i)) * frameOfTangent (s.center (p i)) (s.direction (p i))

/-- The componentwise group elements of a single sampled Hecke word tuple. -/
noncomputable def wordMatrix (w : ProductSample (lattice 1) elliptic I n) (i : I) : SL :=
  Hecke.motion (step (lattice 1) elliptic) (w i).1.val (w i).2

omit [Fintype I] in
/-- All component words are cleared at the same depth, including the shorter words. -/
theorem wordMatrix_clears (w : ProductSample (lattice 1) elliptic I n) (i : I) :
    Clears (wordMatrix w i) n := (clears_motion _ _).mono (Nat.le_of_lt_succ (w i).1.isLt)

/-- Center tile before post-translation, using exactly the carry of the moved frame. -/
noncomputable def movedCarry (s : Catalog.SegmentType I) (b : I → gamma 1) (p : Equiv.Perm I)
    (w : ProductSample (lattice 1) elliptic I n) (i : I) : Deck d :=
  (frameCarry (wordMatrix w i * sourceFrame s b p i) : Deck d)

/-- The charted midpoint and direction used by the actual pack-sample bin test. -/
noncomputable def configuration (s : Catalog.SegmentType I) (b : I → gamma 1)
    (p : Equiv.Perm I) (w : ProductSample (lattice 1) elliptic I n) :
    HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) :=
  segmentChart (speed s) p (productPoint (lattice 1) elliptic n (sourceFrame s b p) w)

/-- All represented centers lie in the product of the closed base Dirichlet tiles. -/
def window (I : Type*) : Set (HyperbolicHost I) := {x | ∀ i, x i ∈ dirichlet 1}

/-- The tie-resolved position window for relative frames, with boundary representatives
assigned before classifying cables by tile. -/
def relativeWindow (I : Type*) : Set (HyperbolicHost I) := {x | ∀ i, x i ∈ planeTile 0}

omit [Fintype I] in
/-- The Borel relative window lies in the common compact Dirichlet window. -/
theorem relativeWindow_subset : relativeWindow I ⊆ window I := fun _ hx i => (hx i).1

omit [Fintype I] in
/-- The common center window is compact. -/
theorem window_compact : IsCompact (window I) := by
  have hc := isCompact_univ_pi (fun _ : I => dirichlet_compact 1)
  convert hc.image (PiLp.continuous_toLp 2 (fun _ : I => ℍ)) using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x,fun i _ => hx i,rfl⟩
  · rintro ⟨v,hv,rfl⟩ i
    exact hv i (mem_univ i)

/-- The actual center lies in the exact position tile in every factor. -/
theorem configuration_center (s : Catalog.SegmentType I) (b : I → gamma 1)
    (p : Equiv.Perm I) (w : ProductSample (lattice 1) elliptic I n) (i : I) :
    (configuration s b p w).1 i ∈ planeTile 0 :=
  relativeFrame_mem (wordMatrix w i * sourceFrame s b p i)

/-- The relative direction tested by the bins has exactly unit product norm. -/
theorem configuration_unit (s : Catalog.SegmentType I) (b : I → gamma 1)
    (p : Equiv.Perm I) (w : ProductSample (lattice 1) elliptic I n) :
    ‖(configuration s b p w).2‖ = 1 := by
  have he (i : I) : ‖(configuration s b p w).2 i‖ = ‖s.direction (p i)‖ := by
    change ‖‖s.direction (p i)‖ • ((positionAngle _).2 : ℂ)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),Circle.norm_coe,mul_one]
  have eq : ‖(configuration s b p w).2‖^2 = ‖s.direction‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp_rw [he]
    exact Equiv.sum_comp p (fun j => ‖s.direction j‖^2)
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp eq).trans s.unit

omit [Fintype I] in
/-- The product of a deck post-translation and a sampled word is a valid surface motion. -/
theorem sample_clears (s : PackSample (lattice 1) elliptic I d n) (i : I) :
    Clears (gammaSL 1 (s.2.2 i).out * wordMatrix s.2.1 i) n := by
  simpa using (clears_lattice 1 (g := gammaSL 1 (s.2.2 i).out) ⟨_,rfl⟩).mul (wordMatrix_clears s.2.1 i)

/-- Apply the full sample, including its factor permutation and left post-translation,
to one point. The same function acts on every site of a pack. -/
noncomputable def sampleMove (s : PackSample (lattice 1) elliptic I d n) :
    SurfaceHost I (d+2*n) → SurfaceHost I d := productMotion d s.1 (sample_clears s)

omit [Fintype I] in
/-- Direct image on lifts before relative normalization, for use on retained sites. -/
theorem sampleMove_projection (s : PackSample (lattice 1) elliptic I d n) (x : HyperbolicHost I) :
    sampleMove s (productProjection _ x) =
      productProjection d (translatePoint (fun i => (s.2.2 i).out) (Catalog.motion s.1 (wordMatrix s.2.1) x)) := by
  ext1 i
  change projectPoint d ((gammaSL 1 (s.2.2 i).out * wordMatrix s.2.1 i) • x (s.1 i)) = _
  rw [mul_smul]; rfl

private theorem project_equal_reps (a b : gamma 1) (e : (a : Deck d) = b) (x : ℍ) :
    projectPoint d (gammaSL 1 a • x) = projectPoint d (gammaSL 1 b • x) := by
  have h := QuotientGroup.eq.mp e
  have h' : b.val * a.val⁻¹ ∈ gamma d := (gammaNormal d).mem_comm h
  apply Quotient.sound
  refine ⟨⟨b.val*a.val⁻¹,h'⟩,?_⟩
  change gammaSL 1 (b*a⁻¹) • (gammaSL 1 a • x) = _
  rw [map_mul,map_inv,mul_smul,inv_smul_smul]

/-- The integral representative used for installing a canonical site at a sampled
absolute tile. -/
noncomputable def deckRep (t : I → Deck d) (i : I) : gamma 1 := (t i).out

/-- Both signs of the whole moved geodesic are reconstructed by the actual relative
chart and a *single* absolute tile shift. This equality also holds at intermediate times. -/
theorem projects_line (s : Catalog.SegmentType I) (b : I → gamma 1)
    (sample : PackSample (lattice 1) elliptic I d n) (t : ℝ) :
    let conf := configuration s b sample.1 sample.2.1
    let tile := shiftedAddress sample.2.2 (movedCarry s b sample.1 sample.2.1)
    sampleMove sample (productProjection (d+2*n) (translatePoint b (shiftTo s.center (productLine s.direction t)))) =
      productProjection d (translatePoint (deckRep tile) (shiftTo conf.1 (productLine conf.2 t))) := by
  intro conf tile
  let p := sample.1
  let w := sample.2.1
  let f (i : I) := wordMatrix w i * sourceFrame s b p i
  let rel (i : I) := relativeFrame (f i)
  have hsrc := framePoint_ofTangent s.center s.direction t
  have hchart : framePoint (speed s ∘ p) rel t = shiftTo conf.1 (productLine conf.2 t) :=
    framePoint_chart _ (fun i => norm_nonneg _) rel t
  rw [← hsrc,← hchart]
  ext1 i
  let z := tangentLine 1 (t * speed s (p i))
  change projectPoint d ((gammaSL 1 (sample.2.2 i).out * wordMatrix w i) •
    (gammaSL 1 (b (p i)) • (frameOfTangent (s.center (p i)) (s.direction (p i)) • z))) =
    projectPoint d (gammaSL 1 (deckRep tile i) • (rel i • z))
  have eq : gammaSL 1 (frameCarry (f i)) * rel i = f i := carry_mul_relative _
  have he : (((sample.2.2 i).out * frameCarry (f i) : gamma 1) : Deck d) = deckRep tile i := by
    rw [QuotientGroup.mk_mul,QuotientGroup.out_eq']
    exact (QuotientGroup.out_eq' (tile i)).symm
  have rep := project_equal_reps _ _ he (rel i • z)
  calc
    _ = projectPoint d (gammaSL 1 (sample.2.2 i).out • (f i • z)) := by simp [f,sourceFrame,mul_smul]
    _ = projectPoint d (gammaSL 1 ((sample.2.2 i).out * frameCarry (f i)) • (rel i • z)) := by
      rw [map_mul,mul_smul (gammaSL 1 (sample.2.2 i).out) (gammaSL 1 (frameCarry (f i))) (rel i • z), ← mul_smul (gammaSL 1 (frameCarry (f i))) (rel i) z,eq]
    _ = _ := rep

end Shortening.Framed

end BorderVNP
end Computability
end OAI
