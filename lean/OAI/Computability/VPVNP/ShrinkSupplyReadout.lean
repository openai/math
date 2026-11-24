import OAI.Computability.VPVNP.DegreeRefreshActualStep
import OAI.Computability.VPVNP.ShrinkPayload

/-!
# Reading a surviving motif word at its two packed sites

The subdivisions of a surviving wire occupy numbered outgoing arcs at its
source and numbered incoming arcs at its target. Each of the two packed
sites can reconstruct the original word from its own half-wire fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open SurvivingSlots ShrinkPayload NetworkKernel WireTensor

variable {V H Tag L : Type} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (layout : Bool) (subdiv : Fin 4 → ℕ)

/-- Numbering for the surviving subdivisions and cyclic padding slots. -/
abbrev ShrinkIndex (next : Equiv.Perm (V × Tag)) (d' pad : ℕ) :=
  SlotIndexing (V × Tag) (PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad) L d'
    (paddedSource (endpoint (P.roleBase layout) (sourceRole layout)))
    (paddedTarget (endpoint (P.roleBase layout) (targetRole layout)) next)
    (paddedShift (P.roleDisplacement layout (sourceRole layout) (targetRole layout)))

variable [Fintype V] [Fintype Tag] [Fintype L] {d' pad : ℕ} {next : Equiv.Perm (V × Tag)}
variable (width : P.Motif → Fin 4 → ℕ) (I : P.ShrinkIndex layout subdiv next d' pad)

/-- The output word network on the numbered lifted arcs of a shrinking step. -/
noncomputable abbrev shrinkOutput : Network :=
  Refresh.actualWireGraph I.graph (P.shrinkSlotWidth layout subdiv width I.outgoing)

variable (hpos : ∀ t, 0 < subdiv t) (m : P.Motif) (t : Fin 4)

/-- Concatenate the genuine outgoing slices at the packed source role. -/
def localSurvivingSource
    (z : (P.shrinkOutput layout subdiv width I).Half
      (let s := P.survivingRole layout (sourceRole layout t) m; (packedBase s, s.2.2))) :
    Fin (width m t) → Bool :=
  (sliceWords (width m t) (subdiv t) (hpos t)).symm fun k ↦
    let i : Id P.Motif subdiv := ⟨t, m, k⟩
    let a := P.shrinkArcEquiv layout subdiv I.outgoing (.inl i)
    cast (congrArg (fun n ↦ Fin n → Bool)
      (P.shrinkSlotWidth_genuine layout subdiv width I.outgoing i))
      (z.1 a (P.shrinkArc_endpoints layout subdiv I i).1.symm)

/-- Concatenate the same genuine slices at the packed target role, reading
the incoming half of each arc with its actual lane translation. -/
def localSurvivingTarget
    (z : (P.shrinkOutput layout subdiv width I).Half
      (let s := P.survivingRole layout (targetRole layout t) m; (packedBase s, s.2.2))) :
    Fin (width m t) → Bool :=
  (sliceWords (width m t) (subdiv t) (hpos t)).symm fun k ↦
    let i : Id P.Motif subdiv := ⟨t, m, k⟩
    let a := P.shrinkArcEquiv layout subdiv I.outgoing (.inl i)
    cast (congrArg (fun n ↦ Fin n → Bool)
      (P.shrinkSlotWidth_genuine layout subdiv width I.outgoing i))
      (z.2 a (P.shrinkArc_endpoints layout subdiv I i).2.symm)

variable (x : (m : P.Motif) → (t : Fin 4) → Fin (width m t) → Bool)

/-- The local outgoing readout recovers the original motif word. -/
theorem localSurvivingSource_eval :
    let N := P.shrinkOutput layout subdiv width I
    P.localSurvivingSource layout subdiv width I hpos m t
      (edgeAssignment N.src N.dst (P.shrinkPayloadsEquiv layout subdiv width I.outgoing hpos x) _) =
      x m t := by
  apply (sliceWords (width m t) (subdiv t) (hpos t)).injective
  simp only [localSurvivingSource, Equiv.apply_symm_apply]
  funext k
  exact P.shrinkPayloadsEquiv_genuine layout subdiv width I.outgoing hpos x ⟨t, m, k⟩

/-- The local incoming readout recovers the same original motif word. -/
theorem localSurvivingTarget_eval :
    let N := P.shrinkOutput layout subdiv width I
    P.localSurvivingTarget layout subdiv width I hpos m t
      (edgeAssignment N.src N.dst (P.shrinkPayloadsEquiv layout subdiv width I.outgoing hpos x) _) =
      x m t := by
  apply (sliceWords (width m t) (subdiv t) (hpos t)).injective
  simp only [localSurvivingTarget, Equiv.apply_symm_apply]
  funext k
  exact P.shrinkPayloadsEquiv_genuine layout subdiv width I.outgoing hpos x ⟨t, m, k⟩

end Compression.PackingData

end VPVNP
end Computability
end OAI
