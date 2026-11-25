import OAI.Computability.BorderVNP.CoverLorentzSiteIncidence
import OAI.Computability.BorderVNP.ShortenEpochFramedSegments
import OAI.Computability.BorderVNP.CoverDeckBitArithmetic

/-!
# The actual frames and modular table lookups of a subdivided cable

One real frame and one speed per factor recover both endpoints of each catalog
hop. Transporting these frames uses the same single quaternion motion throughout
a pack. The carries of a fixed catalog slot are computed by the checked modular
quaternion multiplication program at every level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix UpperHalfPlane BorderVNP.Epoch BorderVNP.Cover.Frame
open RationalHitting RationalHitting.StackLanguage

variable {I : Type*} [Fintype I] {L h : ℝ}

/-- The component speeds of a fixed oriented catalog segment. -/
noncomputable def templateSpeed (hh : 0 < h) (t : Hop I L h) (i : I) :=
  ‖(framedHop hh t).direction i‖

/-- The frame locating and orienting this segment in one factor. -/
noncomputable def templateFrame (hh : 0 < h) (t : Hop I L h) (i : I) : SL :=
  frameOfTangent ((framedHop hh t).center i) ((framedHop hh t).direction i)

/-- The fixed tuple of component speeds is normalized to product speed one. -/
theorem templateSpeed_unit (hh : 0 < h) (t : Hop I L h) : ∑ i, templateSpeed hh t i ^ 2 = 1 := by
  rw [show (∑ i, templateSpeed hh t i ^ 2) = ‖(framedHop hh t).direction‖^2 from
    (PiLp.norm_sq_eq_of_L2 _ _).symm,(framedHop hh t).unit,one_pow]

/-- The table's orientation and elapsed time reconstruct both actual segment endpoints. -/
theorem template_endpoints (hh : 0 < h) (t : Hop I L h) :
    framePoint (templateSpeed hh t) (templateFrame hh t) (-(hopLength h t.1/2)) = hopPosition t 0 ∧
    framePoint (templateSpeed hh t) (templateFrame hh t) (hopLength h t.1/2) = hopPosition t 1 := by
  constructor
  · exact (framePoint_ofTangent _ _ _).trans (framedHop hh t).first
  · exact (framePoint_ofTangent _ _ _).trans (framedHop hh t).last

/-- A whole-pack product motion sends the catalog frame tuple to the actual output
geodesic, including the selected factor permutation and the wire's initial tile. -/
theorem motion_template (hh : 0 < h) (t : Hop I L h) (k : ℝ) (b : I → gamma 1)
    {a : ℕ} (d : ℕ) (e : I ≃ I) {g : I → SL} (hg : ∀ i, Clears (g i) a) :
    productMotion d e hg (productProjection (d+2*a)
      (translatePoint b (framePoint (templateSpeed hh t) (templateFrame hh t) k))) =
      productProjection d (framePoint (templateSpeed hh t ∘ e)
        (fun i => g i * (gammaSL 1 (b (e i)) * templateFrame hh t (e i))) k) := by
  apply PiLp.ext
  intro i
  change projectPoint d (g i • (gammaSL 1 (b (e i)) •
    (templateFrame hh t (e i) • tangentLine 1 (k*templateSpeed hh t (e i))))) =
    projectPoint d ((g i * (gammaSL 1 (b (e i)) * templateFrame hh t (e i))) • _)
  rw [mul_smul,mul_smul]
  rfl

/-- For any fixed finite motion list, all relative frames of the resulting hops belong
to a single finite catalog, independently of depth, input tile and factor permutation. -/
theorem finite_moved_template_frames (hh : 0 < h) {a : ℕ} {M : Type*} [Finite M]
    (g : M → SL) (hg : ∀ m, Clears (g m) a) :
    ∃ S : Set SL, S.Finite ∧ ∀ (m : M) (t : Hop I L h) (i : I) (b : gamma 1),
      relativeFrame (g m * (gammaSL 1 b * templateFrame hh t i)) ∈ S := by
  obtain ⟨S,hS,he⟩ := finite_relative_catalog g hg
    (fun ti : Hop I L h × I => templateFrame hh ti.1 ti.2)
  exact ⟨S,hS,fun m t i b => he m (t,i) b⟩

/-- The actual tile name of a translated slot is obtained by one modular
quaternion product in each factor. -/
theorem hop_binaryAddress {t : Hop I L h} (f : ℝ) (d : ℕ) (b : I → gamma 1) (i : I) :
    binaryProduct (⟨7^(d+1),by positivity⟩,
      binaryCoords (d+1) (reduce (d+1) (b i).val.val),
      binaryCoords (d+1) (reduce (d+1) (hopCarry t f i).val.val)) =
    binaryCoords (d+1) (deckAddress (d+1) (productAddress d
      (productProjection (d+1) (translatePoint b (hopPosition t f))) i)).val := by
  rw [binaryProduct_correct,hopAddress]
  change _ = binaryCoords (d+1) (deckAddress (d+1) (reduceMove d b i * reduceMove d (hopCarry t f) i)).val
  rw [map_mul]; rfl

/-- The same single stack program computes a slot address in polynomially many bit steps
at every level; the slot displacement is one fixed entry of the catalog. -/
theorem hop_binary_steps (hh : 0 < h) :
    ∃ p : Procedure code code binaryProduct, ∀ (d : ℕ) (t : Hop I L h) (b : I → gamma 1)
      (i : I), ∃ n ≤ p.bound.eval (80*(d+2)), Eval p.program
        (single p.input (code ((⟨7^(d+1),by positivity⟩,
          binaryCoords (d+1) (reduce (d+1) (b i).val.val),
          binaryCoords (d+1) (reduce (d+1) (centerCarry hh t i).val.val)) : ProductInput)))
        (single p.output (code (binaryCoords (d+1) (deckAddress (d+1) (productAddress d
          (productProjection (d+1) (translatePoint b (framedHop hh t).center)) i)).val))) n := by
  obtain ⟨p,hp⟩ := binaryProduct_bit_steps
  refine ⟨p,?_⟩
  intro d t b i
  obtain ⟨n,hn,he⟩ := hp (d+1) (reduce (d+1) (b i).val.val) (reduce (d+1) (centerCarry hh t i).val.val)
  refine ⟨n,hn,?_⟩
  rw [centerAddress]
  change Eval _ _ (single p.output (code (binaryCoords (d+1)
    (deckAddress (d+1) (reduceMove d b i * reduceMove d (centerCarry hh t) i)).val))) n
  rw [map_mul]
  exact he

end Cover

end BorderVNP
end Computability
end OAI
