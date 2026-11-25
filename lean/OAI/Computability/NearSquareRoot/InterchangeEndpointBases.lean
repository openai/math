import OAI.Computability.NearSquareRoot.InterchangeEndpoint
import OAI.Computability.NearSquareRoot.InterchangeEndpointMatrix

/-! # Bases for the three blocks of a rectangle address

For a rectangle the early and late bases are chosen once, uniformly over the
endpoints. The two main coordinates have order false, true. Packing the
coordinates as one vector is a linear equivalence on the occupied fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix Module

noncomputable section

/-- Concatenating two complete coordinate blocks is an invertible change of layout. -/
def appendCoordinates (a b : ℕ) :
    ((Fin a → ℚ) × (Fin b → ℚ)) ≃ₗ[ℚ] (Fin (a+b) → ℚ) where
  toFun x := Fin.append x.1 x.2
  invFun x := (x ∘ Fin.castAdd b, x ∘ Fin.natAdd a)
  left_inv := by rintro ⟨x,y⟩; exact Prod.ext (funext (Fin.append_left x y)) (funext (Fin.append_right x y))
  right_inv _ := Fin.append_castAdd_natAdd
  map_add' := by
    intro x y
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  map_smul' := by
    intro k x
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i

variable (C E : Type*) [AddCommGroup C] [Module ℚ C] [Module.Finite ℚ C]
  [AddCommGroup E] [Module ℚ E] [Module.Finite ℚ E]

/-- The designated physical order of the query's pair of main fields. -/
def mainCoordinates : (Bool → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  { toFun := fun m => m ∘ finTwoEquiv
    invFun := fun z => z ∘ finTwoEquiv.symm
    left_inv := fun m => funext fun i => congrArg m (finTwoEquiv.apply_symm_apply i)
    right_inv := fun z => funext fun i => congrArg z (finTwoEquiv.symm_apply_apply i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] theorem mainCoordinates_apply (m : Bool → ℚ) (j : Fin 2) :
    mainCoordinates m j = m (finTwoEquiv j) := rfl

/-- Encode an early reserve, main-field pair, and late reserve into the
physical order used by the lower triangular address program. -/
def endpointCoordinates :
    (C × (Bool → ℚ) × E) ≃ₗ[ℚ] (Fin (finrank ℚ C + (2 + finrank ℚ E)) → ℚ) :=
  ((Module.finBasis ℚ C).equivFun.prodCongr
      ((mainCoordinates.prodCongr (Module.finBasis ℚ E).equivFun).trans
        (appendCoordinates 2 (finrank ℚ E)))).trans (appendCoordinates _ _)

theorem endpointCoordinates_apply (c : C) (m : Bool → ℚ) (e : E) :
    endpointCoordinates C E (c,m,e) =
      Fin.append ((Module.finBasis ℚ C).equivFun c)
        (Fin.append (mainCoordinates m) ((Module.finBasis ℚ E).equivFun e)) := rfl

private def middleBasis : Basis (Fin 2) ℚ (Bool → ℚ) :=
  Basis.ofEquivFun mainCoordinates

/-- Matrix of the change from early to main coordinates in the concrete layout. -/
def earlyMatrix (g : C →ₗ[ℚ] Bool → ℚ) : Matrix (Fin 2) (Fin (finrank ℚ C)) ℚ :=
  LinearMap.toMatrix (Module.finBasis ℚ C) middleBasis g

/-- Matrix of the change from main to late coordinates in the concrete layout. -/
def lateMatrix (d : (Bool → ℚ) →ₗ[ℚ] E) : Matrix (Fin (finrank ℚ E)) (Fin 2) ℚ :=
  LinearMap.toMatrix middleBasis (Module.finBasis ℚ E) d

theorem earlyMatrix_mulVec (g : C →ₗ[ℚ] Bool → ℚ) (c : C) :
    earlyMatrix C g *ᵥ ((Module.finBasis ℚ C).equivFun c) = mainCoordinates (g c) := by
  simpa only [earlyMatrix, ← Basis.equivFun_apply, middleBasis, Basis.equivFun_ofEquivFun] using
    (g.toMatrix_mulVec_repr (Module.finBasis ℚ C) middleBasis c)

theorem lateMatrix_mulVec (d : (Bool → ℚ) →ₗ[ℚ] E) (m : Bool → ℚ) :
    lateMatrix E d *ᵥ (mainCoordinates m) = (Module.finBasis ℚ E).equivFun (d m) := by
  simpa only [lateMatrix, ← Basis.equivFun_apply, middleBasis, Basis.equivFun_ofEquivFun] using
    (d.toMatrix_mulVec_repr middleBasis (Module.finBasis ℚ E) m)

/-- In the chosen bases the rational endpoint equivalence is represented by the
unit lower triangular matrix for both orientations and every address. -/
theorem endpointMatrix_coordinates (g : C →ₗ[ℚ] Bool → ℚ) (d : (Bool → ℚ) →ₗ[ℚ] E)
    (x : C × (Bool → ℚ) × E) :
    endpointMatrix (earlyMatrix C g) (lateMatrix E d) *ᵥ endpointCoordinates C E x =
      endpointCoordinates C E (endpointShear g d x) := by
  rcases x with ⟨c,m,e⟩
  change endpointMatrix (earlyMatrix C g) (lateMatrix E d) *ᵥ
    endpointFields ((Module.finBasis ℚ C).equivFun c) (mainCoordinates m) ((Module.finBasis ℚ E).equivFun e) =
    endpointFields ((Module.finBasis ℚ C).equivFun c) (mainCoordinates (m - g c)) ((Module.finBasis ℚ E).equivFun (e + d (m - g c)))
  rw [endpointMatrix_mulVec, earlyMatrix_mulVec, ← map_sub, lateMatrix_mulVec, map_add]

/-- Packing the endpoint's original occupied reserve into the chosen coordinates.
This equivalence is independent of the query. -/
def reserveFieldCoordinates {Z : Type*} [AddCommGroup Z] [Module ℚ Z]
    (reserve : (C × E) ≃ₗ[ℚ] Z) : Z ≃ₗ[ℚ] (Fin (finrank ℚ C + finrank ℚ E) → ℚ) :=
  (reserve.symm.trans ((Module.finBasis ℚ C).equivFun.prodCongr (Module.finBasis ℚ E).equivFun)).trans
    (appendCoordinates _ _)

theorem reserveFieldCoordinates_apply {Z : Type*} [AddCommGroup Z] [Module ℚ Z]
    (reserve : (C × E) ≃ₗ[ℚ] Z) (c : C) (e : E) :
    reserveFieldCoordinates C E reserve (reserve (c,e)) =
      Fin.append ((Module.finBasis ℚ C).equivFun c) ((Module.finBasis ℚ E).equivFun e) := by
  simp [reserveFieldCoordinates, appendCoordinates]

end

section OriginalReserve

variable {h : ℕ} {U : Type*} [Fintype U] [DecidableEq U]
variable (far : U → U → Prop) [DecidableRel far] (p : ℕ)

/-- Flipping the orientation merely exchanges the two readouts. The original
reserve subspace is shared at every use of a given label. -/
theorem gramRead_ker_orientation (s : Bool) (v : Fin h → U) :
    LinearMap.ker (gramRead (fun u u' => if far u u' then 1 else 0) p s v) =
      LinearMap.ker (gramRead (fun u u' => if far u u' then 1 else 0) p false v) := by
  cases s with
  | false => rfl
  | true =>
    ext x
    simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    constructor <;> intro hx b <;> cases b
    · exact hx true
    · exact hx false
    · exact hx true
    · exact hx false

/-- A single unoriented original reserve has exactly `h * card U` coordinates. -/
theorem finrank_gramReserve (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U) :
    finrank ℚ (LinearMap.ker (gramRead (fun u u' => if far u u' then 1 else 0) p false v))
      = h * Fintype.card U := by
  let read := gramRead (fun u u' => if far u u' then 1 else 0) p false v
  have hsur : Function.Surjective read := fun m => ⟨gramEmbed false v m, LinearMap.congr_fun
    (gramRead_comp_embed_farCount far hp false false v v (by simp [hir])) m⟩
  have hd := read.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top] at hd
  simp only [Module.finrank_pi, Fintype.card_bool, card_gramIndex] at hd
  change finrank ℚ (LinearMap.ker read) = h * Fintype.card U
  omega

/-- This basis is selected once for each label, independently of rectangles and
of source or destination orientation. -/
noncomputable def labelReserveBasis (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U) :
    Basis (Fin (h * Fintype.card U)) ℚ
      (LinearMap.ker (gramRead (fun u u' => if far u u' then 1 else 0) p false v)) :=
  Module.finBasisOfFinrankEq ℚ _ (finrank_gramReserve far p hp hir v)

private theorem castCoordinates {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] {P Q : Submodule ℚ V} (h : P = Q) (e : W ≃ₗ[ℚ] P) (x : W) :
    ((e.trans (LinearEquiv.ofEq P Q h) x : Q) : V) = ((e x : P) : V) := rfl

/-- Read the original occupied reserve vector in an endpoint's orientation.
The equality of kernels above means its ambient value stays fixed. -/
noncomputable def originalReserve (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U) (s : Bool) :
    (Fin (h * Fintype.card U) → ℚ) ≃ₗ[ℚ]
      LinearMap.ker (gramRead (fun u u' => if far u u' then 1 else 0) p s v) :=
  (labelReserveBasis far p hp hir v).equivFun.symm.trans
    (LinearEquiv.ofEq _ _ (gramRead_ker_orientation far p s v).symm)

theorem originalReserve_orientation (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U)
    (s : Bool) (x : Fin (h * Fintype.card U) → ℚ) :
    (originalReserve far p hp hir v s x : GramIndex h U → ℚ) =
      ((labelReserveBasis far p hp hir v).equivFun.symm x : GramIndex h U → ℚ) := by
  exact castCoordinates (gramRead_ker_orientation far p s v).symm (labelReserveBasis far p hp hir v).equivFun.symm x

/-- One common decoder and a single reserve preparation at each incident label
work for every main-coordinate pair on that rectangle. The reserve input is
always expressed in the original basis of the label. The query uses only the
two unit triangular shear blocks after preparation. -/
theorem finite_gram_layout {I : Type*} (hp : 0 < p) (hir : ∀ u, ¬far u u)
    (labels : I → Fin h → U) (side : I → Bool) (ref : I)
    (hlayout : HasGramLayout far p labels side ref) :
    ∃ c e : ℕ, c + e = h * Fintype.card U ∧
    ∃ common : (Fin (c+(2+e)) → ℚ) ≃ₗ[ℚ] (GramIndex h U → ℚ),
    ∃ prepare : I → (Fin (h * Fintype.card U) → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ),
    ∃ G : I → Matrix (Fin 2) (Fin c) ℚ, ∃ D : I → Matrix (Fin e) (Fin 2) ℚ,
    ∀ i z m,
      let packed := (appendCoordinates c e).symm (prepare i z)
      common (endpointMatrix (G i) (D i) *ᵥ endpointFields packed.1 (mainCoordinates m) packed.2) =
        ((labelReserveBasis far p hp hir (labels i)).equivFun.symm z : GramIndex h U → ℚ) +
          gramEmbed (side i) (labels i) m := by
  let emb := fun i => gramEmbed (side i) (labels i)
  let read := fun i => gramRead (fun u u' => if far u u' then 1 else 0) p (side i) (labels i)
  let E := differenceSpace emb ref
  obtain ⟨C, common, reserve, hsize, _, hreal⟩ := hlayout
  let g (i) := (read i).comp C.subtype
  let d (i) := differenceMap emb ref i
  let orig (i) := originalReserve far p hp hir (labels i) (side i)
  refine ⟨finrank ℚ C, finrank ℚ E, hsize, (endpointCoordinates C E).symm.trans common,
    fun i => (orig i).trans (reserveFieldCoordinates C E (reserve i)), fun i => earlyMatrix C (g i),
    fun i => lateMatrix E (d i), ?_⟩
  intro i z m
  let ce := (reserve i).symm (orig i z)
  have hcf : reserve i (ce.1, ce.2) = orig i z := (reserve i).apply_symm_apply _
  have hpacked : (appendCoordinates _ _).symm
        (reserveFieldCoordinates C E (reserve i) (orig i z)) =
      ((Module.finBasis ℚ C).equivFun ce.1, (Module.finBasis ℚ E).equivFun ce.2) := by
    change (appendCoordinates _ _).symm (appendCoordinates _ _ _) = _
    exact (appendCoordinates _ _).symm_apply_apply _
  dsimp only [LinearEquiv.trans_apply]
  rw [hpacked]
  change common ((endpointCoordinates C E).symm
      (endpointMatrix (earlyMatrix C (g i)) (lateMatrix E (d i)) *ᵥ
        endpointCoordinates C E (ce.1,m,ce.2))) = _
  rw [endpointMatrix_coordinates, LinearEquiv.symm_apply_apply, hreal, hcf]
  exact congrArg (· + _) (originalReserve_orientation far p hp hir (labels i) (side i) z)

end OriginalReserve

end Interchange

end NearSquareRoot
end Computability
end OAI
