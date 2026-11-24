import OAI.Computability.VPVNP.SlotPacking

/-!
# Translation on the unconsumed lane

In the last part of Appendix C, a common layout commutes with translation
in the remaining lane. Each orbit of actual motifs is represented uniquely
by the motif whose original wire starts at lane zero. A surviving role edge
over that representative lifts with one fixed lane displacement.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {V H Tag L : Type*} {d c : ℕ} [AddCommGroup L]

/-- Move a packed site in its remaining lane, retaining the old base and tag. -/
def translateSite (s : Site V Tag L) (g : L) : Site V Tag L := (s.1,s.2.1,s.2.2 + g)

/-- Move the packed-site component, retaining the slot label and color bits. -/
def translatePosition (p : Position V H Tag L c) (g : L) : Position V H Tag L c :=
  (translateSite p.1 g,p.2)

/-- The action on original arc labels is given in outgoing numbering. -/
def translateArc (a : Arc V H Tag L d c) (g : L) : Arc V H Tag L d c :=
  ((translateSite a.1.1 g,a.1.2),a.2)

@[simp] theorem translateSite_zero (s : Site V Tag L) : translateSite s 0 = s := by
  simp [translateSite]

@[simp] theorem translateSite_add (s : Site V Tag L) (g h : L) :
    translateSite (translateSite s g) h = translateSite s (g + h) := by
  simp [translateSite, add_assoc]

@[simp] theorem translateArc_zero (a : Arc V H Tag L d c) : translateArc a 0 = a := by
  simp [translateArc]

@[simp] theorem translateArc_add (a : Arc V H Tag L d c) (g h : L) :
    translateArc (translateArc a g) h = translateArc a (g + h) := by simp [translateArc]

@[simp] theorem sourcePosition_translate (a : Arc V H Tag L d c) (g : L) :
    sourcePosition (translateArc a g) = translatePosition (sourcePosition a) g := rfl

namespace PackingData

variable (P : PackingData V H Tag L d c)

@[simp] theorem thick_translate (p : Position V H Tag L c) (g : L) :
    P.thick (translatePosition p g) ↔ P.thick p := Iff.rfl

variable [AddCommGroup Tag]

@[simp] theorem siteGraph_translate (s : Site V Tag L) (i : Fin d) (g : L) :
    P.siteGraph.target (translateSite s g,i) =
      (translateSite (P.siteGraph.target (s,i)).1 g,(P.siteGraph.target (s,i)).2) := by
  rcases s with ⟨v,t,l⟩
  simp [siteGraph, translateSite, add_right_comm]
  rfl

@[simp] theorem assignedBundle_translate (x : Position V H Tag L c) (g : L) :
    P.assignedBundle (translatePosition x g) =
      (translateSite (P.assignedBundle x).1 g,(P.assignedBundle x).2) := rfl

variable [AddCommGroup H]

@[simp] theorem actual_translate (a : Arc V H Tag L d c) (g : L) :
    P.actual (translateArc a g) = translateArc (P.actual a) g := by
  rcases a with ⟨⟨s,i⟩,u,h⟩
  simp only [translateArc, actual_apply, siteGraph_translate]
  rfl

/-- Translation on actual arcs restricts to the wires indexing the motifs. -/
def translateMotif (m : P.Motif) (g : L) : P.Motif :=
  ⟨translateArc m.1 g, by simpa only [actual_translate, sourcePosition_translate,
    thick_translate] using m.2⟩

@[simp] theorem translateMotif_zero (m : P.Motif) : P.translateMotif m 0 = m :=
  Subtype.ext (translateArc_zero _)

@[simp] theorem translateMotif_add (m : P.Motif) (g h : L) :
    P.translateMotif (P.translateMotif m g) h = P.translateMotif m (g + h) :=
  Subtype.ext (translateArc_add ..)

@[simp] theorem C_translate (m : P.Motif) (g : L) :
    P.C (P.translateMotif m g) = translatePosition (P.C m) g := by
  by_cases h : P.thick (sourcePosition m.1) <;> simp [C, translateMotif, h]

@[simp] theorem D_translate (m : P.Motif) (g : L) :
    P.D (P.translateMotif m g) = translatePosition (P.D m) g := by
  by_cases h : P.thick (sourcePosition m.1) <;> simp [D, translateMotif, h]

@[simp] theorem bundle_translate (m : P.Motif) (g : L) :
    P.bundle (P.translateMotif m g) = (translateSite (P.bundle m).1 g,(P.bundle m).2) := by
  simp [bundle]

@[simp] theorem roleA_translate (m : P.Motif) (g : L) :
    P.roleA (P.translateMotif m g) = translateSite (P.roleA m) g := by simp [roleA]

@[simp] theorem roleB_translate (m : P.Motif) (g : L) :
    P.roleB (P.translateMotif m g) = translateSite (P.roleB m) g := by simp [roleB]

omit [AddCommGroup H] in
@[simp] theorem placement_translate (layout : Bool) (x : Position V H Tag L c) (g : L) :
    P.placement layout (translatePosition x g) = translateSite (P.placement layout x) g := by
  by_cases h : P.thick x <;> cases layout <;> simp [placement, h] <;> rfl

@[simp] theorem roleD_translate (layout : Bool) (m : P.Motif) (g : L) :
    P.roleD layout (P.translateMotif m g) = translateSite (P.roleD layout m) g := by simp [roleD]

/-- Unconsumed lane of the old wire in its original outgoing numbering. -/
def sourceLane (m : P.Motif) : L := (sourcePosition m.1).1.2.2

@[simp] theorem sourceLane_translate (m : P.Motif) (g : L) :
    P.sourceLane (P.translateMotif m g) = P.sourceLane m + g := rfl

/-- Finite orbit labels for motifs, indexed by representatives at source lane zero. -/
abbrev BaseMotif := {m : P.Motif // P.sourceLane m = 0}

/-- The representative obtained by translating the source back to zero. -/
def baseMotif (m : P.Motif) : P.BaseMotif :=
  ⟨P.translateMotif m (-P.sourceLane m), by simp⟩

@[simp] theorem baseMotif_translate (m : P.Motif) (g : L) :
    P.baseMotif (P.translateMotif m g) = P.baseMotif m := by
  apply Subtype.ext
  simp [baseMotif]

@[simp] theorem baseMotif_coe (m : P.BaseMotif) : P.baseMotif m.1 = m := by
  apply Subtype.ext
  simp [baseMotif,m.2]

/-- A motif is specified by its lane-zero label and the remaining lane. -/
def motifLaneEquiv : P.Motif ≃ P.BaseMotif × L where
  toFun m := (P.baseMotif m,P.sourceLane m)
  invFun a := P.translateMotif a.1.1 a.2
  left_inv m := by simp [baseMotif]
  right_inv a := by rcases a with ⟨m,g⟩; simp [m.2]

@[simp] theorem motifLaneEquiv_symm_apply (m : P.BaseMotif) (g : L) :
    P.motifLaneEquiv.symm (m,g) = P.translateMotif m.1 g := rfl

/-- Reindex an orbit by the lane of any chosen source role of a surviving edge. -/
def roleLaneEquiv (s : P.Motif → Site V Tag L)
    (hs : ∀ m g, s (P.translateMotif m g) = translateSite (s m) g) :
    P.Motif ≃ P.BaseMotif × L where
  toFun m := (P.baseMotif m,(s m).2.2)
  invFun a := P.translateMotif a.1.1 (a.2 - (s a.1.1).2.2)
  left_inv m := by simp [baseMotif, hs, translateSite]
  right_inv a := by rcases a with ⟨m,g⟩; simp [hs,translateSite]

/-- The lift of a surviving edge, enumerated by its source-role lane, has
displacement equal to the difference of the two lane-zero role coordinates. -/
theorem roleLane_endpoints (s t : P.Motif → Site V Tag L)
    (hs : ∀ m g, s (P.translateMotif m g) = translateSite (s m) g)
    (ht : ∀ m g, t (P.translateMotif m g) = translateSite (t m) g)
    (z : P.BaseMotif) (g : L) :
    let m := (P.roleLaneEquiv s hs).symm (z,g)
    s m = ((s z.1).1,(s z.1).2.1,g) ∧
      t m = ((t z.1).1,(t z.1).2.1,g + ((t z.1).2.2 - (s z.1).2.2)) := by
  simp [roleLaneEquiv, hs, ht, translateSite, sub_eq_add_neg, add_left_comm]

end PackingData

end Compression

end VPVNP
end Computability
end OAI
