import OAI.ThreeFlat.Diagonal.CompressorPackingCounts

namespace OAI
/-! # Thin incidences assigned to a bundle

A source incidence at a thin point contributes for every outgoing slot.
An incoming incidence contributes if its original source is thick. The
original slot permutation reconstructs the same demand from either form.
-/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
variable {c d : ℕ} {V H Tag L : Type*}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- An outgoing incidence at a thin source or incoming incidence from a thick source. -/
abbrev Incidence :=
  {x : Arc V H Tag L d c // ¬P.thick (sourcePosition x)} ⊕
  {y : Arc V H Tag L d c // ¬P.thick (sourcePosition y) ∧
    P.thick (sourcePosition (P.actual.symm y))}

def incidenceArc : Incidence P → Arc V H Tag L d c := Sum.elim Subtype.val Subtype.val

def motifEquiv : P.Motif ≃ Incidence P where
  toFun m :=
    if thick : P.thick (sourcePosition m.val) then
      .inr ⟨P.actual m.val, fun h => m.property ⟨thick, h⟩, by simpa using thick⟩
    else .inl ⟨m.val, thick⟩
  invFun
    | .inl x => ⟨x.val, fun h => x.property h.1⟩
    | .inr y => ⟨P.actual.symm y.val, fun h => y.property.1 (by simpa using h.2)⟩
  left_inv m := by
    by_cases h : P.thick (sourcePosition m.val) <;> simp [h]
  right_inv q := by
    rcases q with x | y
    · simp [x.property]
    · simp [y.property.2]

theorem incidenceSource (m : P.Motif) :
    sourcePosition (incidenceArc P (motifEquiv P m)) = P.C m := by
  by_cases h : P.thick (sourcePosition m.val) <;>
    simp [motifEquiv, incidenceArc, PackingData.C, h]

/-- A physical center of the designated thin endpoint is recovered from the
bundle alone. The word and the outgoing or incoming slot number remain free. -/
def center (p : Site V Tag L × Fin d) (i : Fin d) (w : BitWord c) : Arc V H Tag L d c :=
  ((P.offsetSite.symm p.1, i), w, P.slotLabel.symm p.2)

omit [AddCommGroup H] [AddCommGroup L] in
theorem assigned_center (p : Site V Tag L × Fin d) (i : Fin d) (w : BitWord c) :
    P.assignedBundle (sourcePosition (center P p i w)) = p := by
  simp [center, sourcePosition, PackingData.assignedBundle]

omit [AddCommGroup H] [AddCommGroup L] in
theorem center_eq (x : Arc V H Tag L d c) (p : Site V Tag L × Fin d)
    (hx : P.assignedBundle (sourcePosition x) = p) :
    center P p x.1.2 x.2.1 = x := by
  subst p
  simp [center, sourcePosition, PackingData.assignedBundle]

/-- On a fixed bundle the free data are an incident slot and a word with
one prescribed bit (outgoing) or two prescribed bits (incoming). -/
abbrev Choices (p : Site V Tag L × Fin d) :=
  (Σ i : Fin d, {w : BitWord c // ¬P.thick (sourcePosition (center P p i w))}) ⊕
  (Σ i : Fin d, {w : BitWord c // ¬P.thick (sourcePosition (center P p i w)) ∧
    P.thick (sourcePosition (P.actual.symm (center P p i w)))})

def choiceIncidence (p : Site V Tag L × Fin d) : Choices P p → Incidence P
  | .inl ⟨i,w⟩ => .inl ⟨center P p i w.val, w.property⟩
  | .inr ⟨i,w⟩ => .inr ⟨center P p i w.val, w.property⟩

theorem choice_assigned (p : Site V Tag L × Fin d) (s : Choices P p) :
    P.assignedBundle (sourcePosition (incidenceArc P (choiceIncidence P p s))) = p := by
  rcases s with ⟨i,w⟩ | ⟨i,w⟩ <;> exact assigned_center P p i w.val

def incidenceFiberEquiv (p : Site V Tag L × Fin d) :
    {x : Incidence P // P.assignedBundle (sourcePosition (incidenceArc P x)) = p} ≃ Choices P p where
  toFun q := by
    obtain ⟨x,h⟩ := q
    cases x with
    | inl x =>
      have he := center_eq P x.val p h
      exact .inl ⟨x.val.1.2, x.val.2.1, he.symm ▸ x.property⟩
    | inr y =>
      have he := center_eq P y.val p h
      exact .inr ⟨y.val.1.2, y.val.2.1, he.symm ▸ y.property⟩
  invFun s := ⟨choiceIncidence P p s, choice_assigned P p s⟩
  left_inv q := by
    obtain ⟨x,h⟩ := q
    apply Subtype.ext
    cases x with
    | inl x => exact congrArg Sum.inl (Subtype.ext (center_eq P x.val p h))
    | inr y => exact congrArg Sum.inr (Subtype.ext (center_eq P y.val p h))
  right_inv s := by rcases s with ⟨i,w⟩ | ⟨i,w⟩ <;> rfl

/-- The actual fiber of the paper's `bundle` map has the stated incidence
parameterization. Both directions retain the original arc identity. -/
def bundleFiberEquiv (p : Site V Tag L × Fin d) :
    {m : P.Motif // P.bundle m = p} ≃ Choices P p :=
  (Equiv.subtypeEquiv (motifEquiv P) (fun m => by
    change P.assignedBundle (P.C m) = p ↔ _
    rw [incidenceSource])).trans (incidenceFiberEquiv P p)

end ThreeFlat.Diagonal.CompressorPacking

end OAI
