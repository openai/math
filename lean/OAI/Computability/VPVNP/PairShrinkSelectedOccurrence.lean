import OAI.Computability.VPVNP.PairVertexRoleDomains
import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.CompressorLevelOrder

/-! # The selected shrinking state and packed argument at a physical site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRoleDirectory

open Compression CompressorRecords LocalHistory TraversalRoles TraversalRows NodeArguments TreeDecode
open private next_number from OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → K} {hf : B.IsSolution f}

/-- The selected chronological level at a particular scheduled shrink degree. -/
noncomputable def shrinkLevel (i : Fin S.steps) {g : ℕ}
    (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : Z.ShrinkSelection B.shrink) (tape : List Bool) : SelectedLevel B f hf :=
  ⟨_,_,_,_,Z,_,.shrink i rfl Z,sel,tape⟩

/-- Specialize a dependent statement about a selected shrinking level and
its output site to the actual input state, selection and scheduled index. -/
theorem of_selected_shrink
    (P : (v : SelectedLevel B f hf) → (v.pass.step.term v.term).output.Site → Prop)
    (run : ∀ (i : Fin S.steps) (g : ℕ)
      (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
      (sel : Z.ShrinkSelection B.shrink) (tape : List Bool) (u : MapResidentRows.Site Z),
      P (shrinkLevel i Z sel tape) u)
    (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .shrink) : P v u := by
  rcases v with ⟨a,g,b,n,Z,pass,origin,term,tape⟩
  cases origin with
  | shrink i hlen Z =>
    subst g
    exact run i _ Z term tape u
  | refresh => cases h

/-- The operands and numerical ordinal of the map row chosen by this level.
Its input and selection are recovered from the actual stored pass origin. -/
structure ShrinkOccurrence (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site) where
  /-- The degree transition in the fixed block schedule. -/
  i : Fin S.steps
  /-- The number of residual lane coordinates. -/
  lanes : ℕ
  /-- The original state before this transition. -/
  state : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) lanes)
  /-- The admitted choice at each motif of the input state. -/
  selection : state.ShrinkSelection B.shrink
  /-- The native packed output site addressed by the vertex reader. -/
  site : MapResidentRows.Site state
  selected : v = shrinkLevel i state selection v.selector
  index : v.origin.ordinal = i.val
  ordinal : (MapResidentRows.siteIndex state site).val = ((outputOrder v).entries.symm u).val
  /-- The independent input half of this row in both network presentations. -/
  halves : (v.pass.step.term v.term).output.Half u ≃
    (state.shrinkNext B.shrink (S.shrink i) selection).network.Half site
  packed_eq : ∀ z, pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z =
    packed (state.shrinkNext B.shrink (S.shrink i) selection) site (halves z)

/-- Decode the selected output occurrence, preserving its site and chronological ordinal. -/
noncomputable def occurrence (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .shrink) : ShrinkOccurrence v u := by
  rcases v with ⟨a,g,b,n,Z,pass,origin,term,tape⟩
  cases origin with
  | shrink i hlen Z =>
    subst g
    refine ⟨i,_,Z,term,u,rfl,rfl,?_,Equiv.refl _,fun _ => rfl⟩
    exact (next_number Z B.shrink (S.shrink i) term (packedSiteEquiv.symm u)).symm
  | refresh => cases h

/-- Resolve a physically decoded shrinking-row address to its kernel operands. -/
noncomputable abbrev ShrinkSite.occurrence {passes : List (SelectedLevel B f hf)} (x : ShrinkSite passes) :=
  ShrinkRoleDirectory.occurrence passes[x.val.1] x.val.2 x.property

/-- The native output state read at a recovered shrinking occurrence. -/
noncomputable abbrev ShrinkOccurrence.nextState {v : SelectedLevel B f hf}
    {u : (v.pass.step.term v.term).output.Site} (x : ShrinkOccurrence v u) :=
  x.state.shrinkNext B.shrink (S.shrink x.i) x.selection

/-- Both directions on independent output half assignments of the real map row. -/
noncomputable def halfEquiv (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .shrink) : (v.pass.step.term v.term).output.Half u ≃
      (occurrence v u h).nextState.network.Half (occurrence v u h).site :=
  (occurrence v u h).halves

/-- The address-level conversion preserves the literal packed bit list,
including the ordering of the incoming and outgoing halves. -/
theorem halfEquiv_packed (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .shrink) (z : (v.pass.step.term v.term).output.Half u) :
    pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z =
      packed (occurrence v u h).nextState (occurrence v u h).site (halfEquiv v u h z) :=
  (occurrence v u h).packed_eq z

end PairSimulation.ShrinkRoleDirectory

end VPVNP
end Computability
end OAI
