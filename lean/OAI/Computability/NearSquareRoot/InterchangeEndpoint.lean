import OAI.Computability.NearSquareRoot.InterchangeGram
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel

/-!
# Common address coordinates on a directed rectangle

After orienting the two fields at each endpoint, every mutual Gram block is
the identity. Abstractly, each readout is a left inverse to *every* embedding.
The resulting coordinate system arranges the common complement early, the
two query fields in the middle, and the differences of the oriented vectors
late. This order permits earlier fields to control changes to later fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

variable {K V R I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup R] [Module K R]

/-- Differences of all oriented endpoint embeddings from the reference. -/
def differenceSpace (emb : I → R →ₗ[K] V) (ref : I) : Submodule K V :=
  ⨆ i, LinearMap.range (emb i - emb ref)

theorem differenceSpace_le_ker (emb : I → R →ₗ[K] V) (read : I → V →ₗ[K] R)
    (h : ∀ i j x, read i (emb j x) = x) (ref i : I) :
    differenceSpace emb ref ≤ LinearMap.ker (read i) := by
  refine iSup_le fun j _ ⟨x, hx⟩ => ?_
  rw [← hx]
  simp [h]

/-- Coordinates of the change of oriented pair, expressed in the late reserve. -/
def differenceMap (emb : I → R →ₗ[K] V) (ref i : I) :
    R →ₗ[K] differenceSpace emb ref :=
  (emb i - emb ref).codRestrict _ fun x =>
    (le_iSup (fun j => LinearMap.range (emb j - emb ref)) i) ⟨x, rfl⟩

/-- The common layout is an actual coordinate isomorphism. Its middle block
is the reference pair and its late block is the entire difference space. -/
theorem exists_commonCoordinates (emb : I → R →ₗ[K] V) (read : I → V →ₗ[K] R)
    (h : ∀ i j x, read i (emb j x) = x) (ref : I) :
    ∃ C : Submodule K V, ∃ common : (C × R × differenceSpace emb ref) ≃ₗ[K] V,
      ∀ c m e, common (c, m, e) = (c : V) + (emb ref m + e) := by
  classical
  let E := differenceSpace emb ref
  let U := LinearMap.range (emb ref) ⊔ E
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  let g : (C × R × E) →ₗ[K] V := C.subtype.coprod ((emb ref).coprod E.subtype)
  have hker : E ≤ LinearMap.ker (read ref) := differenceSpace_le_ker emb read h ref ref
  have hi : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    rintro ⟨c, m, e⟩ hx
    change (c : V) + (emb ref m + (e : V)) = 0 at hx
    have hu : emb ref m + (e : V) ∈ U := Submodule.add_mem_sup ⟨m, rfl⟩ e.property
    have hc : (c : V) = 0 := by
      have hcu : (c : V) ∈ U := by
        rw [eq_neg_of_add_eq_zero_left hx]
        exact U.neg_mem hu
      exact hC.disjoint.le_bot ⟨hcu, c.property⟩
    have hre : read ref (e : V) = 0 := hker e.property
    have hx' : emb ref m + (e : V) = 0 := by simpa [hc] using hx
    have hm : m = 0 := by
      simpa [h, hre] using congrArg (read ref) hx'
    have he : (e : V) = 0 := by simpa [hm] using hx'
    exact Prod.ext (Subtype.ext hc) (Prod.ext hm (Subtype.ext he))
  have hs : Function.Surjective g := by
    intro v
    have hv : v ∈ C ⊔ U := by rw [hC.symm.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, u, hu, hcu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨m', ⟨m, hm⟩, e, he, hme⟩ := Submodule.mem_sup.mp hu
    exact ⟨(⟨c,hc⟩, m, ⟨e,he⟩), by change c + (emb ref m + e) = v; rw [hm, hme, hcu]⟩
  exact ⟨C, LinearEquiv.ofBijective g ⟨hi, hs⟩, fun _ _ _ => rfl⟩

section Shear

variable {C E : Type*} [AddCommGroup C] [Module K C] [AddCommGroup E] [Module K E]

/-- Query-dependent lower triangular change to the shared layout. The early
coordinates stay fixed. The middle coordinates only read the early block.
The late coordinates add a shift controlled by the updated middle block. -/
def endpointShear (g : C →ₗ[K] R) (d : R →ₗ[K] E) :
    (C × R × E) ≃ₗ[K] (C × R × E) where
  toFun := fun (c,m,e) => (c, m - g c, e + d (m - g c))
  invFun := fun (c,m,e) => (c, m + g c, e - d m)
  left_inv := by rintro ⟨c,m,e⟩; simp
  right_inv := by rintro ⟨c,m,e⟩; simp
  map_add' := by
    rintro ⟨c,m,e⟩ ⟨c',m',e'⟩
    simp [map_sub]
    constructor <;> abel
  map_smul' := by
    rintro a ⟨c,m,e⟩
    simp [smul_sub, smul_add]

end Shear

/-- At an endpoint the lower triangular change followed by the common layout
expresses the lifted complement, that endpoint's main fields, and the late
reserve. The two query fields are arbitrary coordinates of the type `R`. -/
theorem common_endpointShear (emb : I → R →ₗ[K] V) (read : I → V →ₗ[K] R)
    (ref i : I) (C : Submodule K V)
    (common : (C × R × differenceSpace emb ref) ≃ₗ[K] V)
    (hc : ∀ c m e, common (c,m,e) = (c : V) + (emb ref m + e))
    (c : C) (m : R) (e : differenceSpace emb ref) :
    common (endpointShear ((read i).comp C.subtype) (differenceMap emb ref i) (c,m,e)) =
      ((c : V) - emb i (read i c)) + emb i m + (e : V) := by
  change common (c, m - read i c, e + differenceMap emb ref i (m - read i c)) = _
  rw [hc]
  change (c : V) + (emb ref (m - read i c) + ((e : V) +
    (emb i (m - read i c) - emb ref (m - read i c)))) = _
  rw [map_sub (emb i)]
  abel

/-- The lifted early coordinates together with the late coordinates give all
of the endpoint's reserved fields. This identifies the endpoint change that
is prepared once before the individual queries are run. -/
theorem exists_reserveCoordinates (emb : I → R →ₗ[K] V) (read : I → V →ₗ[K] R)
    (h : ∀ i j x, read i (emb j x) = x) (ref i : I) (C : Submodule K V)
    (common : (C × R × differenceSpace emb ref) ≃ₗ[K] V)
    (hc : ∀ c m e, common (c,m,e) = (c : V) + (emb ref m + e)) :
    ∃ reserve : (C × differenceSpace emb ref) ≃ₗ[K] LinearMap.ker (read i),
      ∀ c e, (reserve (c,e) : V) = ((c : V) - emb i (read i c)) + e := by
  let E := differenceSpace emb ref
  let lift := C.subtype - (emb i).comp ((read i).comp C.subtype)
  let F := (endpointShear ((read i).comp C.subtype) (differenceMap emb ref i)).trans common
  have hF (c : C) (m : R) (e : E) :
      F (c,m,e) = ((c : V) - emb i (read i c)) + emb i m + (e : V) :=
    common_endpointShear emb read ref i C common hc c m e
  have he (e : E) : read i (e : V) = 0 := differenceSpace_le_ker emb read h ref i e.property
  let g := (lift.coprod E.subtype).codRestrict (LinearMap.ker (read i)) (by
    rintro ⟨c,e⟩
    change read i (((c : V) - emb i (read i c)) + (e : V)) = 0
    simp [h, he])
  have hzero (c : C) (e : E) : F (c,0,e) = (g (c,e) : V) := by
    rw [hF, map_zero, add_zero]
    rfl
  have hi : Function.Injective g := by
    rintro ⟨c,e⟩ ⟨c',e'⟩ hce
    have hp := F.injective ((hzero c e).trans ((congrArg Subtype.val hce).trans (hzero c' e').symm))
    exact Prod.ext (congrArg (fun v : C × R × E => v.1) hp) (congrArg (fun v => v.2.2) hp)
  have hs : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨⟨c,m,e⟩, hce⟩ := F.surjective v
    have hm : m = 0 := by
      have hr := congrArg (read i) hce
      rw [hF] at hr
      simpa [h, he, show read i v = 0 from hv] using hr
    subst m
    exact ⟨(c,e), Subtype.ext ((hzero c e).symm.trans hce)⟩
  exact ⟨LinearEquiv.ofBijective g ⟨hi, hs⟩, fun _ _ => rfl⟩


/-- Exact occupied reserve layout in the rational Gram realization for these endpoints. -/
def HasGramLayout {h : ℕ} {U : Type*} [Fintype U] [DecidableEq U]
    (far : U → U → Prop) [DecidableRel far] (p : ℕ)
    (labels : I → Fin h → U) (side : I → Bool) (ref : I) : Prop :=
    let emb := fun i => gramEmbed (side i) (labels i)
    let read := fun i => gramRead (fun u v => if far u v then 1 else 0) p (side i) (labels i)
    let E := differenceSpace emb ref
    ∃ C : Submodule ℚ (GramIndex h U → ℚ),
    ∃ common : (C × (Bool → ℚ) × E) ≃ₗ[ℚ] (GramIndex h U → ℚ),
    ∃ reserve : (i : I) → (C × E) ≃ₗ[ℚ] LinearMap.ker (read i),
      Module.finrank ℚ C + Module.finrank ℚ E = h * Fintype.card U ∧
      (∀ c m e, common (c,m,e) = (c : GramIndex h U → ℚ) + (emb ref m + e)) ∧
      ∀ i c m e, common (endpointShear ((read i).comp C.subtype) (differenceMap emb ref i) (c,m,e))
        = (reserve i (c,e) : GramIndex h U → ℚ) + emb i m

/-- The common and endpoint layouts of a rectangle of the explicit rational
Gram realization. The two reserves use exactly the number of coordinates
available outside the two main fields. Both maps operate on occupied data;
their equivalence proofs apply to every choice of field values. -/
theorem gram_rectangle_layout {h : ℕ} {U : Type*} [Fintype U] [DecidableEq U]
    (far : U → U → Prop) [DecidableRel far] {p : ℕ} (hp : 0 < p)
    (labels : I → Fin h → U) (side : I → Bool) (ref : I)
    (counts : ∀ i j, (Finset.univ.filter fun k => far (labels i k) (labels j k)).card =
      if side i = side j then 0 else p) :
    HasGramLayout far p labels side ref := by
  classical
  dsimp only [HasGramLayout]
  let emb := fun i => gramEmbed (side i) (labels i)
  let read := fun i => gramRead (fun u v => if far u v then 1 else 0) p (side i) (labels i)
  have hall (i j : I) (x : Bool → ℚ) : read i (emb j x) = x := by
    exact LinearMap.congr_fun
      (gramRead_comp_embed_farCount far hp (side i) (side j) _ _ (counts i j)) x
  obtain ⟨C, common, hc⟩ := exists_commonCoordinates emb read hall ref
  choose reserve hr using fun i => exists_reserveCoordinates emb read hall ref i C common hc
  refine ⟨C, common, reserve, ?_, hc, ?_⟩
  · have hd := common.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_bool, card_gramIndex] at hd
    change Module.finrank ℚ C + Module.finrank ℚ (differenceSpace emb ref) = h * Fintype.card U
    omega
  · intro i c m e
    rw [common_endpointShear emb read ref i C common hc, hr]
    abel

/-- Concrete specialization to the occupied sources and destinations of a
Hamming rectangle. The reference is any chosen endpoint of that rectangle. -/
theorem hamming_endpoint_layout {h p k : ℕ} (hp : 0 < p)
    (r : FarRectangles.LabelKey h p k hp)
    (labels : I → FarRectangles.Label h k) (side : I → Bool) (ref : I)
    (hinc : ∀ i, FarRectangles.LabelIncident (side i) r (labels i)) :
    HasGramLayout (fun u v => hammingDist u v = p) p labels side ref := by
  apply gram_rectangle_layout _ hp
  intro i j
  have hi := hinc i
  have hj := hinc j
  cases hsi : side i <;> cases hsj : side j <;> rw [hsi] at hi <;> rw [hsj] at hj
  · exact FarRectangles.count_far_same_side hi hj
  · exact FarRectangles.count_far_across hi hj
  · simpa only [hammingDist_comm, Bool.true_eq_false, ite_false] using
      FarRectangles.count_far_across hj hi
  · exact FarRectangles.count_far_same_side hi hj

end Interchange

end NearSquareRoot
end Computability
end OAI
