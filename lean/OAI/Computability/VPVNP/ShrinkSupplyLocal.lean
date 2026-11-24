import OAI.Computability.VPVNP.ShrinkRoles
import OAI.Computability.VPVNP.ShrinkSupplyReadout
import OAI.Computability.VPVNP.RAMSerialization

/-!
# Reading a six-party supply map at its packed site

The four surviving wires are read from the contiguous slices incident at the
site. Each absorbed wire is read from the single internal index at its owner.
This reconstructs both endpoint columns of every map in the shrinking layout,
including when the half-wire indices on the output graph are independent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

/-- Indices of the four absorbed wires of each motif. -/
abbrev internalLabel {M : Type} (width : M → Bool × Fin 4 → ℕ) (layout : Bool)
    (e : M × Fin 4) := Fin (2 ^ width e.1 (!layout,e.2))

/-- Read one of two dependent fields, according to its layout bit. -/
private def layoutCases (F : Bool → Type*) :
    (l : Bool) → F l → F (!l) → (b : Bool) → F b
  | false, x, _, false => x
  | false, _, y, true => y
  | true, _, y, false => y
  | true, x, _, true => x

private theorem layoutCases_active (F : Bool → Type*) (l : Bool) (x : F l) (y : F (!l)) :
    layoutCases F l x y l = x := by cases l <;> rfl

private theorem layoutCases_absorbed (F : Bool → Type*) (l : Bool) (x : F l) (y : F (!l)) :
    layoutCases F l x y (!l) = y := by cases l <;> rfl

/-- Split all eight motif labels into the surviving words and the four
internally summed indices. -/
private def splitSupply {M : Type} (width : M → Bool × Fin 4 → ℕ) (layout : Bool) :
    ((m : M) → (e : Bool × Fin 4) → Fin (2 ^ width m e)) ≃
      ((m : M) → (t : Fin 4) → Fin (width m (layout,t)) → Bool) ×
        ((e : M × Fin 4) → internalLabel width layout e) where
  toFun x := (fun m t ↦ RAMSerialization.wordBits _ (x m (layout,t)),
    fun e ↦ x e.1 (!layout,e.2))
  invFun z m e := layoutCases (fun l ↦ (t : Fin 4) → Fin (2 ^ width m (l,t))) layout
    (fun t ↦ (RAMSerialization.wordBits _).symm (z.1 m t)) (fun t ↦ z.2 (m,t)) e.1 e.2
  left_inv x := by
    funext m ⟨l,t⟩
    by_cases h : l = layout
    · subst l
      simp only [layoutCases_active, Equiv.symm_apply_apply]
    · rw [Bool.eq_not_of_ne h]
      simp only [layoutCases_absorbed]
  right_inv z := by
    apply Prod.ext
    · funext m t
      simp only [layoutCases_active, Equiv.apply_symm_apply]
    · funext e
      simp only [layoutCases_absorbed]

end Compression.ShrinkMotif

namespace Compression.PackingData

open ShrinkMotif SurvivingSlots NetworkKernel WireTensor

variable {V H Tag L : Type} {c d d' pad : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (width : P.Motif → Bool × Fin 4 → ℕ) {next : Equiv.Perm (V × Tag)}
variable (I : P.ShrinkIndex layout subdiv next d' pad) (hpos : ∀ t, 0 < subdiv t)
variable [Fintype V] [Fintype Tag] [Fintype L]

local notation "N" => P.shrinkOutput layout subdiv (fun m t ↦ width m (layout,t)) I

/-- Reindex a sum over all shared supply labels by one shared assignment
to the output graph and one shared index per absorbed edge. -/
noncomputable def shrinkAssignmentsEquiv :
    ((m : P.Motif) → (e : Bool × Fin 4) → Fin (2 ^ width m e)) ≃
      ((a : (N).Edge) → (N).Payload a) × ((e : P.Motif × Fin 4) → internalLabel width layout e) :=
  (splitSupply width layout).trans ((P.shrinkPayloadsEquiv layout subdiv
    (fun m t ↦ width m (layout,t)) I.outgoing hpos).prodCongr (Equiv.refl _))

theorem shrinkAssignmentsEquiv_apply (x : (m : P.Motif) → (e : Bool × Fin 4) → Fin (2 ^ width m e)) :
    P.shrinkAssignmentsEquiv layout subdiv width I hpos x =
      (P.shrinkPayloadsEquiv layout subdiv (fun m t ↦ width m (layout,t)) I.outgoing hpos
        (fun m t ↦ RAMSerialization.wordBits _ (x m (layout,t))), fun e : P.Motif × Fin 4 ↦ x e.1 (!layout,e.2)) :=
  rfl

variable (m : P.Motif) (j : Fin 6)

private def readSupplyEnd (endParty : Bool × Fin 4 → Fin 6) (role : Fin 4 → PackedRole)
    (active : ∀ t, partyRole layout (endParty (layout,t)) = role t)
    (absorbed : ∀ t, partyRole layout (endParty (!layout,t)) = internalRole layout t)
    (readWord : (t : Fin 4) → (N).Half (packedSiteEquiv (P.survivingRole layout (role t) m)) →
      Fin (width m (layout,t)) → Bool)
    (h : Placed (P.shrinkInternalOwner layout) (internalLabel width layout) (P.shrinkPartySite layout m j))
    (z : (N).Half (P.shrinkPartySite layout m j)) (e : Bool × Fin 4) :
    j = endParty e → Fin (2 ^ width m e) :=
  layoutCases (fun l ↦ (t : Fin 4) → j = endParty (l,t) → Fin (2 ^ width m (l,t))) layout
    (fun t hj ↦
      let hs := congrArg (fun r ↦ packedSiteEquiv (P.survivingRole layout r m))
        ((congrArg (partyRole layout) hj).trans (active t))
      (RAMSerialization.wordBits _).symm (readWord t
        ⟨fun a ha ↦ z.1 a (hs.trans ha), fun a ha ↦ z.2 a (hs.trans ha)⟩))
    (fun t hj ↦ h (m,t) (congrArg (fun r ↦ packedSiteEquiv (P.survivingRole layout r m))
      ((congrArg (partyRole layout) hj).trans (absorbed t)))) e.1 e.2

/-- All columns of the supply basis at a party, using only half-wires
and absorbed indices available at that party's packed site. -/
noncomputable def shrinkLocalSupplyArg
    (h : Placed (P.shrinkInternalOwner layout) (internalLabel width layout) (P.shrinkPartySite layout m j))
    (z : (N).Half (P.shrinkPartySite layout m j)) :
    ((e : Bool × Fin 4) → j = supply.src e → Fin (2 ^ width m e)) ×
      ((e : Bool × Fin 4) → j = supply.dst e → Fin (2 ^ width m e)) :=
  ⟨P.readSupplyEnd layout subdiv width I m j supply.src (sourceRole layout)
    (role_src_survives layout) (role_src_absorbed layout)
    (P.localSurvivingSource layout subdiv _ I hpos m) h z,
   P.readSupplyEnd layout subdiv width I m j supply.dst (targetRole layout)
    (role_dst_survives layout) (role_dst_absorbed layout)
    (P.localSurvivingTarget layout subdiv _ I hpos m) h z⟩

private theorem readSupplyEnd_eval (endParty : Bool × Fin 4 → Fin 6) (role : Fin 4 → PackedRole)
    (active : ∀ t, partyRole layout (endParty (layout,t)) = role t)
    (absorbed : ∀ t, partyRole layout (endParty (!layout,t)) = internalRole layout t)
    (readWord : (t : Fin 4) → (N).Half (packedSiteEquiv (P.survivingRole layout (role t) m)) →
      Fin (width m (layout,t)) → Bool)
    (x : (m : P.Motif) → (e : Bool × Fin 4) → Fin (2 ^ width m e)) (z : (a : (N).Edge) → (N).Payload a)
    (heval : ∀ t, readWord t (edgeAssignment (N).src (N).dst z _) =
      RAMSerialization.wordBits _ (x m (layout,t))) :
    P.readSupplyEnd layout subdiv width I m j endParty role active absorbed readWord
      (fun e _ ↦ x e.1 (!layout,e.2)) (edgeAssignment (N).src (N).dst z _) = fun e _ ↦ x m e := by
  funext ⟨l,t⟩ hj
  by_cases hl : l = layout
  · subst l
    simp only [readSupplyEnd, layoutCases_active]
    change (RAMSerialization.wordBits _).symm (readWord t (edgeAssignment (N).src (N).dst z _)) = _
    rw [heval, Equiv.symm_apply_apply]
  · have hl' := Bool.eq_not_of_ne hl
    subst l
    simp only [readSupplyEnd, layoutCases_absorbed]

/-- A shared assignment gives exactly the original motif column at every
party after slicing the surviving words and placing the absorbed indices. -/
theorem shrinkLocalSupplyArg_eval (x : (m : P.Motif) → (e : Bool × Fin 4) → Fin (2 ^ width m e)) :
    P.shrinkLocalSupplyArg layout subdiv width I hpos m j (fun e _ ↦ x e.1 (!layout,e.2))
      (edgeAssignment (N).src (N).dst (P.shrinkPayloadsEquiv layout subdiv _ I.outgoing hpos
        (fun m t ↦ RAMSerialization.wordBits _ (x m (layout,t)))) _) =
      edgeAssignment supply.src supply.dst (x m) j := by
  apply Prod.ext
  · exact P.readSupplyEnd_eval layout subdiv width I m j supply.src _
      (role_src_survives layout) (role_src_absorbed layout) _ x _
      (fun t ↦ P.localSurvivingSource_eval layout subdiv _ I hpos m t _)
  · exact P.readSupplyEnd_eval layout subdiv width I m j supply.dst _
      (role_dst_survives layout) (role_dst_absorbed layout) _ x _
      (fun t ↦ P.localSurvivingTarget_eval layout subdiv _ I hpos m t _)

end Compression.PackingData

end VPVNP
end Computability
end OAI
