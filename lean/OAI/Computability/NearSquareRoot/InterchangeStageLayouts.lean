import OAI.Computability.NearSquareRoot.InterchangeEndpointBases

/-!
# Label coordinates and the commuting rectangle address maps

An original label stores the full reserve in one fixed basis. Reversing the
orientation exchanges only the two main fields of the query. The coordinates
of a rectangle are related to these label coordinates by its query-independent
reserve preparation and the unit lower triangular endpoint change.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Module Matrix

noncomputable section

/-- A split readout gives coordinates consisting of its kernel and the oriented main pair. -/
private def splitRead {K V M : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup M] [Module K M] (read : V →ₗ[K] M) (emb : M →ₗ[K] V)
    (h : Function.LeftInverse read emb) : (LinearMap.ker read × M) ≃ₗ[K] V where
  toFun x := (x.1 : V) + emb x.2
  invFun y := (⟨y - emb (read y), by simp [LinearMap.mem_ker, h _]⟩, read y)
  left_inv x := by
    rcases x with ⟨z,m⟩
    have hz : read (z : V) = 0 := z.property
    exact Prod.ext (Subtype.ext <| by simp [hz, h _]) (by simp [hz, h _])
  right_inv y := by simp
  map_add' x y := by simp; abel
  map_smul' _ _ := by simp [smul_add]

variable {h : ℕ} {U : Type*} [Fintype U] [DecidableEq U]
variable (far : U → U → Prop) [DecidableRel far] (p : ℕ)

local notation "reserveWidth" => h * Fintype.card U

/-- The original source or destination address in the global Gram coordinates.
All endpoints for this label use the same original reserve basis. -/
def labelCoordinates (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U) (side : Bool) :
    ((Fin reserveWidth → ℚ) × (Bool → ℚ)) ≃ₗ[ℚ] (GramIndex h U → ℚ) :=
  ((originalReserve far p hp hir v side).prodCongr (LinearEquiv.refl ℚ _)).trans <|
    splitRead (gramRead (fun u u' => if far u u' then 1 else 0) p side v)
      (gramEmbed side v) fun x => LinearMap.congr_fun
        (gramRead_comp_embed_farCount far hp side side v v (by simp [hir])) x

theorem labelCoordinates_apply (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U)
    (side : Bool) (z : Fin reserveWidth → ℚ) (m : Bool → ℚ) :
    labelCoordinates far p hp hir v side (z,m) =
      ((labelReserveBasis far p hp hir v).equivFun.symm z : GramIndex h U → ℚ) +
        gramEmbed side v m := by
  change (originalReserve far p hp hir v side z : GramIndex h U → ℚ) + _ = _
  exact congrArg (· + gramEmbed side v m) (originalReserve_orientation far p hp hir v side z)

omit [Fintype U] in
private theorem gramEmbed_flip (v : Fin h → U) (m : Bool → ℚ) :
    gramEmbed true v (fun b => m (!b)) = gramEmbed false v m := by
  simp [gramEmbed, Fintype.linearCombination_apply, add_comm]

/-- The diagonal source-to-destination transport is exactly the query swap on
the pair; every coordinate of the original reserve stays fixed. -/
theorem labelCoordinates_diagonal (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U)
    (z : Fin reserveWidth → ℚ) (m : Bool → ℚ) :
    (labelCoordinates far p hp hir v true).symm (labelCoordinates far p hp hir v false (z,m)) =
      (z,fun b => m (!b)) := by
  apply (labelCoordinates far p hp hir v true).injective
  rw [LinearEquiv.apply_symm_apply, labelCoordinates_apply, labelCoordinates_apply,
    gramEmbed_flip]


/-- Physical order of the original active fields: early reserve, first main field,
second main field. -/
def unpackQuery (a : ℕ) : (Fin (a + 2) → ℚ) ≃ₗ[ℚ] ((Fin a → ℚ) × (Bool → ℚ)) :=
  (appendCoordinates a 2).symm.trans ((LinearEquiv.refl ℚ _).prodCongr mainCoordinates.symm)

/-- One fixed ordering of the ambient Gram coordinates for all rectangles and labels. -/
def gramOrder (h : ℕ) (U : Type*) [Fintype U] :
    (GramIndex h U → ℚ) ≃ₗ[ℚ] (Fin (h * Fintype.card U + 2) → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ)
    (Fintype.equivFinOfCardEq (by rw [card_gramIndex, add_comm]))

/-- The source and destination changes as square address matrices on their occupied
fields. The ordering of the common address does not depend on the orientation. -/
def labelAddress (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U) (side : Bool) :
    (Fin (reserveWidth+2) → ℚ) ≃ₗ[ℚ] (Fin (reserveWidth+2) → ℚ) :=
  ((unpackQuery reserveWidth).trans (labelCoordinates far p hp hir v side)).trans (gramOrder h U)

/-- Swap the last two active coordinates. -/
def flipQuery (a : ℕ) : Equiv.Perm (Fin (a+2)) :=
  Equiv.swap (Fin.natAdd a 0) (Fin.natAdd a 1)

private theorem unpack_flip (a : ℕ) (x : Fin (a+2) → ℚ) :
    unpackQuery a (x ∘ flipQuery a) =
      ((unpackQuery a x).1,fun b => (unpackQuery a x).2 (!b)) := by
  apply Prod.ext
  · funext i
    change x (Equiv.swap _ _ (Fin.castAdd 2 i)) = x (Fin.castAdd 2 i)
    rw [Equiv.swap_apply_of_ne_of_ne]
    all_goals intro h; have hh := congrArg Fin.val h; simp at hh; omega
  · funext b
    cases b
    · change x ((Equiv.swap _ _) (Fin.natAdd a (0 : Fin 2))) = x (Fin.natAdd a 1)
      rw [Equiv.swap_apply_left]
    · change x ((Equiv.swap _ _) (Fin.natAdd a (1 : Fin 2))) = x (Fin.natAdd a 0)
      rw [Equiv.swap_apply_right]

theorem labelAddress_diagonal (hp : 0 < p) (hir : ∀ u, ¬far u u) (v : Fin h → U)
    (x : Fin (reserveWidth+2) → ℚ) :
    (labelAddress far p hp hir v true).symm (labelAddress far p hp hir v false x) =
      x ∘ flipQuery reserveWidth := by
  apply (labelAddress far p hp hir v true).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [labelAddress, LinearEquiv.trans_apply]
  apply (gramOrder h U).congr_arg
  change labelCoordinates far p hp hir v false (unpackQuery reserveWidth x) =
    labelCoordinates far p hp hir v true (unpackQuery reserveWidth (x ∘ flipQuery reserveWidth))
  rw [unpack_flip]
  exact ((LinearEquiv.apply_symm_apply _ _).symm.trans (congrArg
    (labelCoordinates far p hp hir v true)
    (labelCoordinates_diagonal far p hp hir v (unpackQuery reserveWidth x).1 (unpackQuery reserveWidth x).2)))

/-- Rectangle coordinates after the query-independent preparation. The difference
block has moved past the main coordinates and its displaced spares are spectators. -/
def preparedQuery {a c e : ℕ} (prepare : (Fin a → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ)) :
    (Fin (a+2) → ℚ) ≃ₗ[ℚ] (Fin (c+(2+e)) → ℚ) :=
  (appendCoordinates a 2).symm.trans <|
    ((prepare.trans (appendCoordinates c e).symm).prodCongr (LinearEquiv.refl ℚ _)).trans <|
    (LinearEquiv.prodAssoc ℚ (Fin c → ℚ) (Fin e → ℚ) (Fin 2 → ℚ)).trans <|
    ((LinearEquiv.refl ℚ _).prodCongr ((LinearEquiv.prodComm ℚ _ _).trans
      (appendCoordinates 2 e))).trans (appendCoordinates c _)

/-- The lower triangular endpoint part as an automorphism over any commutative ring. -/
def endpointAddress {R : Type*} [CommRing R] {c b e : ℕ}
    (G : Matrix (Fin b) (Fin c) R) (D : Matrix (Fin e) (Fin b) R) :
    (Fin (c+(b+e)) → R) ≃ₗ[R] (Fin (c+(b+e)) → R) :=
  (endpointMatrix G D).toLinearEquiv' (IsUnit.nonempty_invertible
    ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_of_isLowerTriangular _ (endpointMatrix_lower G D)]
      simp [endpointMatrix_diagonal]))).some

@[simp] theorem endpointAddress_apply {R : Type*} [CommRing R] {c b e : ℕ}
    (G : Matrix (Fin b) (Fin c) R) (D : Matrix (Fin e) (Fin b) R) (x : Fin (c+(b+e)) → R) :
    endpointAddress G D x = endpointMatrix G D *ᵥ x := rfl

/-- Commutative address diagram of a Gram rectangle, with the same global source
and destination used at every incidence of the same oriented label. -/
theorem rectangle_address_diagram {I : Type*} (hp : 0 < p) (hir : ∀ u, ¬far u u)
    (labels : I → Fin h → U) (side : I → Bool) (ref : I)
    (hrect : HasGramLayout far p labels side ref) :
    ∃ c e : ℕ, c + e = reserveWidth ∧
    ∃ common : (Fin (c+(2+e)) → ℚ) ≃ₗ[ℚ] (Fin (reserveWidth+2) → ℚ),
    ∃ prepare : I → (Fin reserveWidth → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ),
    ∃ G : I → Matrix (Fin 2) (Fin c) ℚ, ∃ D : I → Matrix (Fin e) (Fin 2) ℚ,
      ∀ i, (preparedQuery (prepare i)).trans ((endpointAddress (G i) (D i)).trans common) =
        labelAddress far p hp hir (labels i) (side i) := by
  obtain ⟨c,e,hd,common,prep,G,D,hg⟩ := finite_gram_layout far p hp hir labels side ref hrect
  refine ⟨c,e,hd,common.trans (gramOrder h U),prep,G,D, fun i => ?_⟩
  apply LinearEquiv.ext
  intro x
  simp only [labelAddress, LinearEquiv.trans_apply]
  apply (gramOrder h U).congr_arg
  let z := ((unpackQuery reserveWidth) x).1
  let m := ((unpackQuery reserveWidth) x).2
  change common (endpointMatrix (G i) (D i) *ᵥ preparedQuery (prep i) x) =
    labelCoordinates far p hp hir (labels i) (side i) (z,m)
  rw [labelCoordinates_apply, ← hg i z m]
  congr 2
  have hm : mainCoordinates m = ((appendCoordinates reserveWidth 2).symm x).2 :=
    LinearEquiv.apply_symm_apply _ _
  rw [hm]
  rfl

end

end Interchange

end NearSquareRoot
end Computability
end OAI
