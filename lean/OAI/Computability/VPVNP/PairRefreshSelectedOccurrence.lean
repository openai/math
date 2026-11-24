import OAI.Computability.VPVNP.PairShrinkRoleDirectory
import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentSite

/-! # Refresh rows of a selected execution

The native site order identifies a refresh output with a base, residual lane
and promoted port. Unpacking the origin of the chosen pass recovers the input
state and term that produced this row. The numerical directory uses the same
ordinal and distinguishes repeated occurrences of a term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords
open TraversalRoles TraversalRows PortRefresh ShrinkRoleDirectory

variable {k K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
  {B : S.Templates} {f : B.Entry → K} {hf : B.IsSolution f}

/-- Output sites whose selected pass is a refresh, indexed by their chronological level. -/
abbrev Row (passes : List (SelectedLevel B f hf)) :=
  {x : ShrinkRoleDirectory.Site passes // tagLevel B f hf passes[x.1] = .refresh}

/-- The literal selected-level record determined by a refresh origin. -/
noncomputable def level {g : ℕ} (X : State S.portExponent (S.portExponent + g))
    (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (bits : List Bool) :
    SelectedLevel B f hf :=
  ⟨_, _, _, _, X, _, .refresh X, choice, bits⟩

/-- Typed input state, branch choice, and physical port of an output row. -/
structure Occurrence (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site) where
  /-- Number of lanes remaining after port promotion. -/
  lanes : ℕ
  /-- Input state recorded at this occurrence. -/
  state : State S.portExponent (S.portExponent + lanes)
  /-- Refresh term selected by the branch. -/
  choice : DyadicRefreshChoice state S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh
  /-- Base, residual lane and promoted port of the output site. -/
  port : (state.Base × BitWord lanes) × Fin (2 ^ S.portExponent)
  selected : v = level state choice v.selector
  ordinal : (NewSlots.sites state.baseIndex (bitWordFinEquiv lanes) port).val =
    ((outputOrder v).entries.symm u).val

/-- Decompose the recorded origin and undo the port promotion on the actual
output site. The shrink branch is ruled out by the stored role. -/
noncomputable def occurrence (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .refresh) : Occurrence v u := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    refine ⟨_, X, term, promotedSites.symm u, rfl, ?_⟩
    rcases u with ⟨⟨base, port⟩, lane⟩
    rfl

/-- The typed refresh data at this chronological output row. -/
noncomputable abbrev Row.occurrence {passes : List (SelectedLevel B f hf)} (x : Row passes) :=
  SelectedRows.occurrence passes[x.val.1] x.val.2 x.property

private def asRefresh (passes : List (SelectedLevel B f hf)) (x : ShrinkRoleDirectory.Site passes) :
    Option (Row passes) :=
  if h : tagLevel B f hf passes[x.1] = .refresh then some ⟨x, h⟩ else none

private theorem asRefresh_eq_some (passes : List (SelectedLevel B f hf))
    (x : ShrinkRoleDirectory.Site passes) (y : Row passes) :
    asRefresh passes x = some y ↔ x = y.val := by
  unfold asRefresh
  split
  · rw [Option.some.injEq, Subtype.ext_iff]
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun e => h (e ▸ y.property)

variable (base : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf)) {w : ℕ}

/-- The typed row returned by matching a popped word to a physical output
header and checking the chosen pass's role. -/
noncomputable def decode (node : BurstRAM.Word w) : Option (Row passes) :=
  (OutputRowDirectory.decode B.recordLimit base leaf (outputTags passes) node).bind fun x =>
    asRefresh passes ((siteRows passes).symm x)

theorem decode_eq_some_iff
    (fit : layerBase B.recordLimit base (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)
    (node : BurstRAM.Word w) (x : Row passes) :
    decode base leaf passes node = some x ↔
      node.val = ShrinkRoleDirectory.address B.recordLimit base leaf passes x.val := by
  have room : layerBase B.recordLimit base (leaf :: outputTags passes)
      ((outputTags passes).length + 1) ≤ 2 ^ w := by simpa only [outputTags, List.length_map] using fit
  rw [decode, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨row, found, tagged⟩
    have he := (asRefresh_eq_some passes _ x).mp tagged
    have same : row = siteRows passes x.val := by rw [← he, Equiv.apply_symm_apply]
    exact (OutputRowDirectory.decode_eq_some_iff B.recordLimit base leaf (outputTags passes) room
      node _).mp (same ▸ found)
  · intro addr
    refine ⟨siteRows passes x.val, ?_, ?_⟩
    · exact (OutputRowDirectory.decode_eq_some_iff B.recordLimit base leaf (outputTags passes) room node _).mpr addr
    · exact (asRefresh_eq_some passes _ x).mpr (Equiv.symm_apply_apply _ _)

/-- A parent address selects a unique chronological refresh occurrence. -/
theorem unique_row {x y : Row passes}
    (same : ShrinkRoleDirectory.address B.recordLimit base leaf passes x.val =
      ShrinkRoleDirectory.address B.recordLimit base leaf passes y.val) : x = y :=
  Subtype.ext (address_injective B.recordLimit base leaf passes same)

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
