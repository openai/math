import OAI.Hierarchy.DescentCommonPalette

namespace OAI
/-! # Transport of physical rotor sites, edges and fibre ordinals -/

namespace Hierarchy.DescentCommonPalette
open Computability.BorderVNP.Crossing DescentPhysicalSplit DescentRotor DescentRotor.Physical
open scoped Classical
noncomputable section

private theorem count_eq_of_fibre_equiv {d d' : ℕ} {p q : Type} [Fintype p] [Fintype q]
    {b : p → ℕ} {b' : q → ℕ} (N : Network d p b) (M : Network d' q b')
    (v : N.Site) (v' : M.Site) (e : Fibre N v ≃ Fibre M v') : count N v = count M v' :=
  Fintype.card_congr e

variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (D R C w u : ℕ)
local notation "bare" => host G.arcs 0 0 0 0 0
local notation "cfg" => host G.arcs D R C w u

/-- The two fibres have the same cardinality because both enumerate the actual
two terminals and the directed host half-edges at the same vertex. -/
theorem rotor_count_eq (v : Fin (2^n)) : count bare v = count cfg v :=
  count_eq_of_fibre_equiv bare cfg v v
    ((rowFibre (D:=0) (R:=0) (C:=0) (w:=0) (u:=0) G v).trans
      (rowFibre (D:=D) (R:=R) (C:=C) (w:=w) (u:=u) G v).symm)

/-- Forward site transport preserves both end labels and the ordinal of each tap. -/
def rotorSiteEquiv : (rotor G).Site ≃ (graph cfg).Site where
  toFun := rotorSite G D R C w u
  invFun
    | ⟨v,.inl side⟩ => ⟨v,.inl side⟩
    | ⟨v,.inr i⟩ => ⟨v,.inr (Fin.cast (rotor_count_eq G D R C w u v).symm i)⟩
  left_inv := by
    rintro ⟨v, side | i⟩ <;> rfl
  right_inv := by
    rintro ⟨v, side | i⟩ <;> rfl

/-- Forward edge transport keeps every original host cable and its orientation,
and preserves the vertex and the ordinal of each spine cable. -/
def rotorEdgeEquiv : (rotor G).Edge ≃ (graph cfg).Edge where
  toFun := rotorEdge G D R C w u
  invFun
    | .inl e => .inl e
    | .inr ⟨v,k⟩ =>
      .inr ⟨v, Fin.cast (congrArg (fun m : ℕ => m+1) (rotor_count_eq G D R C w u v).symm) k⟩
  left_inv := by
    rintro (e | ⟨v,k⟩) <;> rfl
  right_inv := by
    rintro (e | ⟨v,k⟩) <;> rfl

@[simp] theorem rotorSite_tapIndex (v : Fin (2^n)) (i : Fin (count bare v)) :
    rotorSite G D R C w u ⟨v,.inr i⟩ =
      ⟨v,.inr (Fin.cast (rotor_count_eq G D R C w u v) i)⟩ := rfl

@[simp] theorem rotorSiteEquiv_symm_tapIndex (v : Fin (2^n)) (i : Fin (count cfg v)) :
    (rotorSiteEquiv G D R C w u).symm ⟨v,.inr i⟩ =
      ⟨v,.inr (Fin.cast (rotor_count_eq G D R C w u v).symm i)⟩ := rfl

@[simp] theorem rotorEdge_cable (e : (bare).Edge) :
    rotorEdge G D R C w u (.inl e) = .inl e := rfl

@[simp] theorem rotorEdge_spine (v : Fin (2^n)) (i : Fin (count bare v+1)) :
    rotorEdge G D R C w u (.inr ⟨v,i⟩) =
      .inr ⟨v, Fin.cast (congrArg (fun m : ℕ => m+1) (rotor_count_eq G D R C w u v)) i⟩ := rfl

@[simp] theorem rotorEdgeEquiv_symm_cable (e : (cfg).Edge) :
    (rotorEdgeEquiv G D R C w u).symm (.inl e) = .inl e := rfl

@[simp] theorem rotorEdgeEquiv_symm_spine (v : Fin (2^n)) (i : Fin (count cfg v+1)) :
    (rotorEdgeEquiv G D R C w u).symm (.inr ⟨v,i⟩) =
      .inr ⟨v, Fin.cast (congrArg (fun m : ℕ => m+1) (rotor_count_eq G D R C w u v).symm) i⟩ := rfl

private theorem inverse_endpoint {E E' S S' : Type} (edges : E ≃ E') (sites : S ≃ S')
    (before : E → S) (after : E' → S')
    (forward : ∀ e, after (edges e) = sites (before e)) (e' : E') :
    sites.symm (after e') = before (edges.symm e') := by
  obtain ⟨e,rfl⟩ := edges.surjective e'
  rw [forward e, sites.symm_apply_apply, edges.symm_apply_apply]

theorem rotor_left_inv (e : (graph cfg).Edge) :
    (rotorSiteEquiv G D R C w u).symm ((graph cfg).src e) =
      (rotor G).src ((rotorEdgeEquiv G D R C w u).symm e) :=
  inverse_endpoint (rotorEdgeEquiv G D R C w u) (rotorSiteEquiv G D R C w u)
    (rotor G).src (graph cfg).src (rotor_left G D R C w u) e

theorem rotor_right_inv (e : (graph cfg).Edge) :
    (rotorSiteEquiv G D R C w u).symm ((graph cfg).dst e) =
      (rotor G).dst ((rotorEdgeEquiv G D R C w u).symm e) :=
  inverse_endpoint (rotorEdgeEquiv G D R C w u) (rotorSiteEquiv G D R C w u)
    (rotor G).dst (graph cfg).dst (rotor_right G D R C w u) e

theorem rotor_pin_inv (p : Pin (2^n)) :
    (rotorSiteEquiv G D R C w u).symm ((graph cfg).attach p) = (rotor G).attach p :=
  (congrArg (rotorSiteEquiv G D R C w u).symm (rotor_pin G D R C w u p)).trans
    ((rotorSiteEquiv G D R C w u).symm_apply_apply _)

/-- Every named terminal and each oriented end of each host cable commute with
the forward site map. This uses the public endpoint and pin equations. -/
theorem rotor_tap (x : Leg bare) : tap cfg x = rotorSite G D R C w u (tap bare x) := by
  rcases x with p | ⟨e,side⟩
  · exact rotor_pin G D R C w u p
  · cases side with
    | false => exact rotor_left G D R C w u (.inl e)
    | true => exact rotor_right G D R C w u (.inl e)

/-- Casting the slot ordinal across the two row fibres preserves the physical
leg it names, including its orientation in the presence of loops. -/
@[simp] theorem rotor_name_cast (v : Fin (2^n)) (i : Fin (count bare v)) :
    name cfg v (Fin.cast (rotor_count_eq G D R C w u v) i) = name bare v i := by
  apply tap_injective cfg
  let j := Fin.cast (rotor_count_eq G D R C w u v) i
  have named : (tap cfg (name cfg v j) : (graph cfg).Site) = ⟨v,.inr j⟩ := tap_named cfg v j
  have slot : (⟨v,.inr j⟩ : (graph cfg).Site) = rotorSite G D R C w u ⟨v,.inr i⟩ :=
    (rotorSite_tapIndex G D R C w u v i).symm
  have carried := congrArg (rotorSite G D R C w u) (tap_named bare v i)
  exact named.trans (slot.trans (carried.symm.trans (rotor_tap G D R C w u (name bare v i)).symm))

/-- The index of the same named and oriented leg in the two fibres is the
transport of the original index. -/
theorem rotor_index_cast (v : Fin (2^n)) (x : Fibre bare v) (y : Fibre cfg v)
    (same : y.val = x.val) :
    index cfg v y = Fin.cast (rotor_count_eq G D R C w u v) (index bare v x) := by
  apply (index cfg v).symm.injective
  apply Subtype.ext
  have cfgName : (name cfg v (index cfg v y) : Leg cfg) = y.val :=
    congrArg (fun z : Fibre cfg v => (z.val : Leg cfg)) ((index cfg v).symm_apply_apply y)
  have bareName : (name bare v (index bare v x) : Leg cfg) = x.val :=
    congrArg (fun z : Fibre bare v => (z.val : Leg cfg)) ((index bare v).symm_apply_apply x)
  exact cfgName.trans (same.trans (bareName.symm.trans
    (rotor_name_cast G D R C w u v (index bare v x)).symm))

end
end Hierarchy.DescentCommonPalette

end OAI
