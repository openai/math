import OAI.Computability.BorderVNP.CoverRelativePlacement
import OAI.Computability.BorderVNP.CoverLorentzSubdivision
import OAI.Computability.BorderVNP.ShortenEpochSegments

/-!
# Finite relative point and segment catalogs

Normalize a point in each surface factor to its actual tie-resolved base
tile. A bounded wire whose endpoints have catalogued relative positions
then has only finitely many types: the second endpoint differs from its
representative by an integral displacement of bounded length. This works
for quotient wires using a separate distance-realizing lift for each one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Catalog

open Cover Cover.Frame Epoch Hecke Set UpperHalfPlane
open scoped Pointwise

variable {I : Type*}

/-- Integral translation from a lifted point's tile to the base tile. -/
noncomputable def toTile (x : HyperbolicHost I) : I → gamma 1 :=
  fun i => Frame.toBaseTile (x i)

/-- Product of the exact relative endpoint positions. -/
noncomputable def normalize (x : HyperbolicHost I) := translatePoint (toTile x) x

/-- Relative endpoint of a quotient point; this is independent of its lift. -/
noncomputable def relative (d : ℕ) (x : SurfaceHost I (d+1)) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => relativePosition d (x i)

/-- Projection commutes with taking the relative endpoint in every factor. -/
theorem relative_projection (d : ℕ) (x : HyperbolicHost I) :
    relative d (productProjection (d+1) x) = normalize x := rfl

private theorem translate_mul (a b : I → gamma 1) (x : HyperbolicHost I) :
    translatePoint (a*b) x = translatePoint a (translatePoint b x) := by
  ext1 i
  change gammaSL 1 (a i*b i) • x i = gammaSL 1 (a i) • (gammaSL 1 (b i) • x i)
  rw [map_mul,mul_smul]

private theorem translate_inv (a : I → gamma 1) (x : HyperbolicHost I) :
    translatePoint a⁻¹ (translatePoint a x) = x := by
  ext1 i
  change gammaSL 1 (a i)⁻¹ • (gammaSL 1 (a i) • x i) = x i
  rw [map_inv, inv_smul_smul]

/-- An integral tile translation changes only the address, even at a seam. -/
theorem normalize_translate (a : I → gamma 1) (x : HyperbolicHost I) :
    normalize (translatePoint a x) = normalize x := by
  ext1 i
  change gammaSL 1 (Frame.toBaseTile (gammaSL 1 (a i) • x i)) • (gammaSL 1 (a i) • x i) = _
  rw [Frame.toBaseTile_smul, map_mul, map_inv, mul_smul, inv_smul_smul]
  rfl

/-- Full product motion on the lifted positions, including the factor permutation. -/
noncomputable def motion (σ : Equiv.Perm I) (g : I → SL) (x : HyperbolicHost I) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => g i • x (σ i)

variable [Fintype I]

/-- A finite catalog of relative sites survives every choice in a fixed finite
motion list, uniformly over input lifts, tile addresses, level and deck translation. -/
theorem finite_moved_points {M : Type*} [Finite M] {a : ℕ}
    (σ : M → Equiv.Perm I) (g : M → I → SL) (clear : ∀ m i, Clears (g m i) a)
    {S : Set (HyperbolicHost I)} (hS : S.Finite) :
    ∃ R : Set (HyperbolicHost I), R.Finite ∧ ∀ m x, normalize x ∈ S →
      ∀ deck : I → gamma 1, normalize (translatePoint deck (motion (σ m) (g m) x)) ∈ R := by
  classical
  let := hS.fintype
  obtain ⟨F,hF,hrel⟩ := finite_relative_catalog
    (fun z : M × I => g z.1 z.2) (fun z => clear z.1 z.2)
    (fun z : S × I => (z.1.val z.2).toSL2R)
  let := hF.fintype
  let coord := fun f : I → F => WithLp.toLp 2 (fun i => (f i).val • UpperHalfPlane.I)
  refine ⟨range coord, finite_range coord, ?_⟩
  intro m x hx deck
  rw [normalize_translate]
  let j := σ m
  let lift := fun i => (toTile x (j i))⁻¹
  let z := fun i => g m i * (gammaSL 1 (lift i) * ((normalize x) (j i)).toSL2R)
  have hf (i) : relativeFrame (z i) ∈ F := hrel (m,i) (⟨normalize x,hx⟩,j i) (lift i)
  refine ⟨fun i => ⟨_,hf i⟩, ?_⟩
  ext1 i
  change relativeFrame (z i) • UpperHalfPlane.I =
    gammaSL 1 (toBaseTile (g m i • x (j i))) • (g m i • x (j i))
  have hz : z i • UpperHalfPlane.I = g m i • x (j i) := by
    change (g m i * (gammaSL 1 ((toTile x (j i))⁻¹) * ((normalize x) (j i)).toSL2R)) •
      UpperHalfPlane.I = _
    rw [mul_smul,mul_smul,UpperHalfPlane.toSL2R_smul_I,map_inv]
    exact congrArg (fun p : UpperHalfPlane => g m i • p)
      (inv_smul_smul (gammaSL 1 (toTile x (j i))) (x (j i)))
  rw [relativeFrame,mul_smul,hz]

/-- Both endpoints of a quotient wire are obtained from this one local
lifted type with one common tile translation, preserving their distance. -/
def Realizes {d : ℕ} (x y : SurfaceHost I (d+1)) (t : HyperbolicHost I × HyperbolicHost I) : Prop :=
  ∃ b : I → gamma 1, productProjection (d+1) (translatePoint b t.1) = x ∧
    productProjection (d+1) (translatePoint b t.2) = y ∧ dist t.1 t.2 = dist x y

/-- Bounded quotient wires with endpoints in a finite relative site catalog
have a finite set of ordered, jointly lifted endpoint pairs, uniform in the level. -/
theorem finite_pairs {S : Set (HyperbolicHost I)} (hS : S.Finite) (L : ℝ) :
    ∃ T : Set (HyperbolicHost I × HyperbolicHost I), T.Finite ∧
      ∀ d (x y : SurfaceHost I (d+1)), relative d x ∈ S → relative d y ∈ S →
        dist x y ≤ L → ∃ t ∈ T, Realizes x y t := by
  classical
  obtain ⟨r,hr⟩ := (hS.image (fun z => dist (productOrigin I) z)).bddAbove
  let moves := {k : I → gamma 1 | moveLength k ≤ r+L+r}
  have hm : moves.Finite := finite_bounded_moves _
  let := hS.fintype
  let := hm.fintype
  let f := fun t : S × moves × S => (t.1.val, translatePoint t.2.1.val t.2.2.val)
  refine ⟨range f,finite_range f,?_⟩
  intro d x y hx hy hlen
  obtain ⟨u,hu,_⟩ := productProjection_closest_lift (productOrigin I) x
  obtain ⟨v,hv,hd⟩ := productProjection_closest_lift u y
  rw [hu] at hd
  have hux : normalize u ∈ S := by rw [← relative_projection d u,hu]; exact hx
  have hvy : normalize v ∈ S := by rw [← relative_projection d v,hv]; exact hy
  let k := toTile u * (toTile v)⁻¹
  have hk : translatePoint k (normalize v) = translatePoint (toTile u) v := by
    dsimp only [k,normalize]
    rw [translate_mul,translate_inv]
  have hdist : dist (normalize u) (translatePoint k (normalize v)) = dist x y := by
    rw [hk,normalize,(translatePoint_isometry _).dist_eq,hd]
  have hkm : k ∈ moves := by
    change dist (productOrigin I) (translatePoint k (productOrigin I)) ≤ r+L+r
    have hb := hr (show dist (productOrigin I) (normalize u) ∈ _ from ⟨_,hux,rfl⟩)
    have he := hr (show dist (productOrigin I) (normalize v) ∈ _ from ⟨_,hvy,rfl⟩)
    have hlast : dist (translatePoint k (normalize v)) (translatePoint k (productOrigin I)) ≤ r := by
      rw [(translatePoint_isometry k).dist_eq,dist_comm]; exact he
    linarith only [hb,hlast,hdist,hlen,
      dist_triangle (productOrigin I) (normalize u) (translatePoint k (normalize v)),
      dist_triangle (productOrigin I) (translatePoint k (normalize v)) (translatePoint k (productOrigin I))]
  refine ⟨(normalize u,translatePoint k (normalize v)), ⟨(⟨_,hux⟩,⟨_,hkm⟩,⟨_,hvy⟩),rfl⟩,
    (toTile u)⁻¹, ?_, ?_,hdist⟩
  · change productProjection (d+1) (translatePoint (toTile u)⁻¹ (translatePoint (toTile u) u)) = x
    rw [translate_inv,hu]
  · change productProjection (d+1) (translatePoint (toTile u)⁻¹ (translatePoint k (normalize v))) = y
    rw [hk,translate_inv,hv]

/-- An oriented relative segment as used by the next round's frame motion. -/
structure SegmentType (I : Type*) [Fintype I] where
  /-- Lifted representative center. -/
  center : HyperbolicHost I
  /-- Product unit tangent, including the speeds of all factors. -/
  direction : PiLp 2 (fun _ : I => ℂ)
  /-- Half-length of the segment. -/
  radius : ℝ
  unit : ‖direction‖ = 1
  positive : 0 < radius

/-- Both oriented endpoints of a relative segment type. -/
noncomputable def SegmentType.ends (s : SegmentType I) : HyperbolicHost I × HyperbolicHost I :=
  (shiftTo s.center (productLine s.direction (-s.radius)), shiftTo s.center (productLine s.direction s.radius))

/-- Positive charged wires admit a finite level-independent catalog including
their lengths, midpoint positions and oriented tangent data. -/
theorem finite_segments {S : Set (HyperbolicHost I)} (hS : S.Finite) (L : ℝ) :
    ∃ V : Set (SegmentType I), V.Finite ∧ ∀ d (x y : SurfaceHost I (d+1)),
      relative d x ∈ S → relative d y ∈ S → x ≠ y → dist x y ≤ L →
        ∃ v ∈ V, Realizes x y v.ends := by
  classical
  obtain ⟨T,hT,h⟩ := finite_pairs hS L
  let U := {t ∈ T | t.1 ≠ t.2}
  have hU : U.Finite := hT.subset fun _ ht => ht.1
  let := hU.fintype
  have line (t : U) := exists_product_midpoint_line t.val.1 t.val.2 t.property.2
  choose c v hv hl hr using line
  let f := fun t : U => (⟨c t,v t,dist t.val.1 t.val.2 / 2,hv t,half_pos (dist_pos.mpr t.property.2)⟩ : SegmentType I)
  refine ⟨range f,finite_range f,?_⟩
  intro d x y hx hy hne hb
  obtain ⟨t,ht,realizes⟩ := h d x y hx hy hb
  have hn : t.1 ≠ t.2 := by
    obtain ⟨_,_,_,hd⟩ := realizes
    exact dist_pos.mp (hd.symm ▸ dist_pos.mpr hne)
  let u : U := ⟨t,ht,hn⟩
  refine ⟨f u,⟨u,rfl⟩,?_⟩
  have eq : (f u).ends = t := Prod.ext (hl u) (hr u)
  rw [eq]; exact realizes

end Shortening.Catalog

end BorderVNP
end Computability
end OAI
