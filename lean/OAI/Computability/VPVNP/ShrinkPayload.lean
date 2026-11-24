import OAI.Computability.VPVNP.RegularizedMotifs
import OAI.Computability.VPVNP.WidthRounding
import Mathlib.Algebra.BigOperators.Fin

/-!
# Shared payloads of the shrinking step

Each surviving motif wire in §7.2 is divided into contiguous strings. Its
subdivision labels are numbered at the base by lane-zero motif IDs and then
lifted at the absolute lane of the source role. A padding slot has a unique
empty string. Thus summing shared output-slot assignments is equivalent to
summing one shared word on each original surviving motif wire.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkPayload

open SurvivingSlots

/-- In subdivision order, the bit coordinates of the slices exhaust exactly
the input wire. This includes zero-length slices. -/
def sliceBits (b q : ℕ) (hq : 0 < q) :
    (Σ i : Fin q, Fin (splitWidth b q i)) ≃ Fin b :=
  finSigmaFinEquiv.trans (finCongr (sum_splitWidth b q hq))

/-- Extract all slices of the shared wire word. The inverse concatenates
them in subdivision order. -/
def sliceWords (b q : ℕ) (hq : 0 < q) :
    (Fin b → Bool) ≃ ((i : Fin q) → Fin (splitWidth b q i) → Bool) :=
  ((sliceBits b q hq).symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.piCurry
    (fun (i : Fin q) (_ : Fin (splitWidth b q i)) ↦ Bool))

/-- The start of a slice is the sum of the preceding slice widths. -/
theorem sliceBits_offset (b q : ℕ) (hq : 0 < q) (i : Fin q) (j : Fin (splitWidth b q i)) :
    (sliceBits b q hq ⟨i,j⟩ : ℕ) = (∑ k : Fin i, splitWidth b q (Fin.castLE i.isLt.le k)) + j :=
  finSigmaFinEquiv_apply _

variable {M T D : Type*} (subdiv : T → ℕ) (width : M → T → ℕ)

/-- Classify output widths before outgoing slot numbering. -/
def classWidth : Id M subdiv ⊕ D → ℕ :=
  Sum.elim (fun i ↦ splitWidth (width i.2.1 i.1) (subdiv i.1) i.2.2) (fun _ ↦ 0)

/-- Split all genuine wires and insert the empty word on each padding ID. -/
def classPayloads (hpos : ∀ t, 0 < subdiv t) :
    ((m : M) → (t : T) → Fin (width m t) → Bool) ≃
      ((i : Id M subdiv ⊕ D) → Fin (classWidth subdiv width i) → Bool) where
  toFun x
    | .inl ⟨t,m,k⟩ => sliceWords (width m t) (subdiv t) (hpos t) (x m t) k
    | .inr _ => Fin.elim0
  invFun z m t := (sliceWords (width m t) (subdiv t) (hpos t)).symm (fun k ↦ z (.inl ⟨t,m,k⟩))
  left_inv x := by funext m t; exact (sliceWords ..).symm_apply_apply (x m t)
  right_inv z := by
    funext i
    rcases i with ⟨t,m,k⟩ | dummy
    · exact congrFun ((sliceWords (width m t) (subdiv t) (hpos t)).apply_symm_apply
        (fun j ↦ z (.inl ⟨t,m,j⟩))) k
    · funext j
      exact Fin.elim0 j

end Compression.ShrinkPayload

namespace Compression.PackingData

open SurvivingSlots ShrinkPayload

variable {V H Tag L : Type*} {c d d' pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (width : P.Motif → Fin 4 → ℕ)
variable (outgoing : PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad ≃ (V × Tag) × Fin d')

/-- An actual outgoing arc label is its source site (base and lane) and
slot number. The genuine label retains its motif, type and subdivision,
and the lane of its source role fixes the copy of the numbered base arc. -/
def shrinkArcEquiv :
    (Id P.Motif subdiv ⊕ ((V × Tag) × Fin pad) × L) ≃ ((V × Tag) × L) × Fin d' :=
  let atSource : (((V × Tag) × Fin d') × L) ≃ ((V × Tag) × L) × Fin d' := {
    toFun a := ((a.1.1,a.2),a.1.2)
    invFun a := ((a.1.1,a.2),a.1.2)
    left_inv _ := rfl
    right_inv _ := rfl }
  ((P.survivingLaneEquiv layout subdiv).sumCongr (Equiv.refl _)).trans
    ((Equiv.sumProdDistrib _ _ _).symm.trans ((outgoing.prodCongr (Equiv.refl L)).trans atSource))

/-- Read a genuine numbered outgoing arc in source-lane coordinates. -/
theorem shrinkArcEquiv_genuine (i : Id P.Motif subdiv) :
    P.shrinkArcEquiv layout subdiv outgoing (.inl i) =
      let z := P.survivingLaneEquiv layout subdiv i
      let p := outgoing (.inl z.1)
      ((p.1,z.2),p.2) := rfl

/-- Each dummy ID is repeated at every remaining lane. -/
theorem shrinkArcEquiv_padding (z : (V × Tag) × Fin pad) (g : L) :
    P.shrinkArcEquiv layout subdiv outgoing (.inr (z,g)) =
      (((outgoing (.inr z)).1,g),(outgoing (.inr z)).2) := rfl

/-- Both ends of the numbered genuine wire coincide with its placed motif
roles, including the destination's translated lane and the incoming slot. -/
theorem shrinkArc_endpoints {next : Equiv.Perm (V × Tag)}
    (I : SlotIndexing (V × Tag) (PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad) L d'
      (paddedSource (endpoint (P.roleBase layout) (sourceRole layout)))
      (paddedTarget (endpoint (P.roleBase layout) (targetRole layout)) next)
      (paddedShift (P.roleDisplacement layout (sourceRole layout) (targetRole layout))))
    (i : Id P.Motif subdiv) :
    let a := P.shrinkArcEquiv layout subdiv I.outgoing (.inl i)
    let src := endpoint (P.survivingRole layout) (sourceRole layout) i
    let dst := endpoint (P.survivingRole layout) (targetRole layout) i
    a.1 = (packedBase src,src.2.2) ∧
      (I.graph.actualGraph.target a).1 = (packedBase dst,dst.2.2) := by
  obtain ⟨⟨z,g⟩, rfl⟩ := (P.survivingLaneEquiv layout subdiv).symm.surjective i
  obtain ⟨hs,ht⟩ := P.survivingLane_endpoints layout subdiv z g
  simp only [shrinkArcEquiv_genuine, Equiv.apply_symm_apply, hs, ht, LiftedSlots.actualGraph_target,
    Prod.mk.eta, I.match_eq, I.dst_eq, I.displacement_eq]
  rw [I.src_eq]
  exact ⟨rfl,rfl⟩

/-- The actual lifted widths, indexed by outgoing base port and source lane,
as in `LiftedSlots.actualTarget`. -/
def shrinkSlotWidth (p : ((V × Tag) × Fin d') × L) : ℕ :=
  classWidth subdiv width ((P.shrinkArcEquiv layout subdiv outgoing).symm ((p.1.1,p.2),p.1.2))

/-- At a genuine arc the width is the designated subdivision of the
actual motif wire, including its lane-dependent width. -/
theorem shrinkSlotWidth_genuine (i : Id P.Motif subdiv) :
    let a := P.shrinkArcEquiv layout subdiv outgoing (.inl i)
    P.shrinkSlotWidth layout subdiv width outgoing ((a.1.1,a.2),a.1.2) =
      splitWidth (width i.2.1 i.1) (subdiv i.1) i.2.2 := by
  simp [shrinkSlotWidth, classWidth]

/-- All padding arcs have zero width. -/
theorem shrinkSlotWidth_padding (z : (V × Tag) × Fin pad) (g : L) :
    P.shrinkSlotWidth layout subdiv width outgoing (outgoing (.inr z),g) = 0 := by
  change classWidth subdiv width ((P.shrinkArcEquiv layout subdiv outgoing).symm
    (P.shrinkArcEquiv layout subdiv outgoing (.inr (z,g)))) = 0
  simp [classWidth]

/-- One shared word per original surviving motif wire is equivalent to one
shared word per numbered arc of the padded output graph. Specializing
`outgoing` to `dyadicSurvivingSlots.outgoing` gives the graph of Lemma C.1. -/
def shrinkPayloadsEquiv (hpos : ∀ t, 0 < subdiv t) :
    ((m : P.Motif) → (t : Fin 4) → Fin (width m t) → Bool) ≃
      ((a : ((V × Tag) × L) × Fin d') →
        Fin (P.shrinkSlotWidth layout subdiv width outgoing ((a.1.1,a.2),a.1.2)) → Bool) :=
  (classPayloads subdiv width hpos).trans (Equiv.piCongrLeft'
    (fun i ↦ Fin (classWidth subdiv width i) → Bool) (P.shrinkArcEquiv layout subdiv outgoing))

/-- Looking up a genuine arc in the encoded assignment returns precisely
its slice of the original motif word. -/
theorem shrinkPayloadsEquiv_genuine (hpos : ∀ t, 0 < subdiv t)
    (x : (m : P.Motif) → (t : Fin 4) → Fin (width m t) → Bool) (i : Id P.Motif subdiv) :
    let a := P.shrinkArcEquiv layout subdiv outgoing (.inl i)
    cast (congrArg (fun n ↦ Fin n → Bool)
        (P.shrinkSlotWidth_genuine layout subdiv width outgoing i))
      (P.shrinkPayloadsEquiv layout subdiv width outgoing hpos x a) =
      sliceWords (width i.2.1 i.1) (subdiv i.1) (hpos i.1) (x i.2.1 i.1) i.2.2 := by
  let e := P.shrinkArcEquiv layout subdiv outgoing
  let z := classPayloads (D := ((V × Tag) × Fin pad) × L) subdiv width hpos x
  change cast _ (z (e.symm (e (.inl i)))) = z (.inl i)
  exact cast_eq_iff_heq.mpr (by rw [e.symm_apply_apply])

/-- Numbering and zero-width padding preserve any additive charge on the
widths with zero charge on a dummy. Taking the charge to be squared width
divided by slot mass identifies the actual graph energy in (7.2). -/
theorem sum_shrinkSlotWidth [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    {A : Type*} [AddCommMonoid A] (charge : ℕ → A) (hzero : charge 0 = 0) :
    (∑ a : ((V × Tag) × L) × Fin d',
      charge (P.shrinkSlotWidth layout subdiv width outgoing ((a.1.1,a.2),a.1.2))) =
      ∑ i : Id P.Motif subdiv, charge (splitWidth (width i.2.1 i.1) (subdiv i.1) i.2.2) := by
  classical
  let e := P.shrinkArcEquiv layout subdiv outgoing
  let f (i : Id P.Motif subdiv ⊕ ((V × Tag) × Fin pad) × L) := charge (classWidth subdiv width i)
  change (∑ a, f (e.symm a)) = _
  rw [e.symm.sum_comp f, Fintype.sum_sum_type]
  simp [f, classWidth, hzero]

end Compression.PackingData

end VPVNP
end Computability
end OAI
