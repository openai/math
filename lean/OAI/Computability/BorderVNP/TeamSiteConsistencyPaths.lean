import OAI.Computability.BorderVNP.TeamSiteConsistency
import OAI.Computability.BorderVNP.TeamContractionReadout

/-! # Weight-preserving bijection between genuine native paths and team histories

A raw history stores the individual physical interior bit assignment and the full
choice-labeled events at each processor. Its flattening is the original native path.
Genuine zero paths are included in the first bijection. Restricting both sides to
nonzero weight gives the indexing needed for the accepting-leaf contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP TeamRAM TeamContraction TeamTapeHandoff
open BurstRAM (Word)
variable {teams w p r k a e : ℕ}

/-- Fixed data and word bounds for the physical team implementing a particular RAM. -/
structure Setup (teams w p r k a e : ℕ) where
  /-- The signed instruction table. -/
  program : TeamOpcode.Program p r k a
  /-- Shared public input words. -/
  pub : Fin k → Word w
  /-- Native routines called at the private instructions. -/
  lib : TeamOpcode.Macros w a
  /-- Initial finite-PC control. -/
  start : TeamOpcode.State w p r
  /-- Per-processor charged tick bound. -/
  block : Word w
  /-- Whole-team charged tick bound. -/
  limit : Word w
  /-- Largest admitted consecutive read. -/
  cap : Word w
  /-- Maximum native choice bits at each instruction. -/
  privateClock : ℕ
  /-- Real local memory portions initialized by the processor input parser. -/
  input : Fin teams → List Bool
  /-- Positive processor count. -/
  positive : 0 < teams
  /-- Each finite PC is representable in the transmitted frame. -/
  pcs : p ≤ 2^w
  /-- Sufficient width for physical tags and phase bits. -/
  width : 2 ≤ w+1
  /-- Global sorter indices fit the physical width. -/
  sorter : 2^(Nat.clog 2 teams)*2^e < 2^(w+1)
  /-- All header addresses fit the logical width. -/
  header : (List.ofFn input).flatten.length ≤ 2^w
  /-- Input prefix bound per real processor. -/
  localInput : ∀ j, (input j).length ≤ 3*block.val
  /-- Doubling each logical record fits the physical array. -/
  rowCapacity : 2*block.val ≤ 2^e
  /-- Global ticks fit after allowing idle suffixes at handoff. -/
  schedule : limit.val ≤ teams*(block.val-cap.val)

namespace Setup

variable (g : Setup teams w p r k a e)

/-- Native RAM and its complete initialized input on the same physical layout. -/
def machine : MachineInput w (TeamOpcode.State w p r) :=
  ⟨g.program.fetch g.pub g.lib,g.start,(List.ofFn g.input).flatten.length,
    TeamTapeInputEmit.headerWord w (List.ofFn g.input).flatten⟩

/-- Native accepting paths under the charged, burst and private path bounds. -/
abbrev Paths := NativePath g.machine g.limit.val g.cap.val g.privateClock

/-- The complete semantic histories with an actual interior assignment and all the
physically imposed native resource bounds. -/
abbrev Histories := {z : RawHistory teams r w e //
  let es := (List.ofFn z.blocks).flatten
  z.Valid g.program g.pub g.lib g.start g.block g.limit g.cap g.input g.width g.sorter es (es.map Event.choices) ∧
    Within g.limit.val g.cap.val g.privateClock es}

private theorem unique_raw (path : g.Paths) : ∃! z : RawHistory teams r w e,
    z.Valid g.program g.pub g.lib g.start g.block g.limit g.cap g.input g.width g.sorter path.val
      (path.val.map Event.choices) :=
  (execute_iff_unique_rawHistory g.program g.pub g.lib g.start g.block g.limit g.cap g.input g.positive g.pcs
    g.width g.sorter g.header g.localInput g.rowCapacity _ _ path.property.2.length path.property.2.cost
    (path.property.2.cost.trans g.schedule)).mp path.property.1

private def recover (z : g.Histories) : g.Paths := by
  refine ⟨(List.ofFn z.val.blocks).flatten,?_,z.property.2⟩
  have ok := z.property.1
  have within := z.property.2
  exact (z.val.execute_of_valid g.program g.pub g.lib g.start g.block g.limit g.cap g.input g.positive g.pcs g.width
    g.sorter g.header g.localInput g.rowCapacity _ _ within.length within.cost ok).1

private noncomputable def expand (path : g.Paths) : g.Histories := by
  let z := (g.unique_raw path).exists.choose
  have ok := (g.unique_raw path).exists.choose_spec
  have eq : (List.ofFn z.blocks).flatten = path.val := ok.1.1
  exact ⟨z,eq ▸ ⟨ok,path.property.2⟩⟩

/-- The native path and its unique bit-level shared history are mutually inverse.
The inverse reads the actual chronological list from the local blocks. -/
noncomputable def rawEquivNative : g.Histories ≃ g.Paths where
  toFun := g.recover
  invFun := g.expand
  left_inv z := by
    apply Subtype.ext
    exact (g.unique_raw (g.recover z)).unique (g.unique_raw (g.recover z)).exists.choose_spec z.property.1
  right_inv path := Subtype.ext (g.unique_raw path).exists.choose_spec.1.1

/-- The inverse's native event list is literally the processor-block flattening. -/
theorem rawEquivNative_events (z : g.Histories) : (g.rawEquivNative z).val = (List.ofFn z.val.blocks).flatten := rfl

/-- Signed products agree on every path, including a valid zero-weight history. -/
theorem rawEquivNative_weight (z : g.Histories) : z.val.weight = pathWeight (g.rawEquivNative z).val :=
  z.val.weight_eq

/-- Real raw histories corresponding to accepting nonzero leaves. -/
abbrev NonzeroHistories := { z : g.Histories // z.val.weight ≠ 0 }

/-- Restrict the complete path bijection to the nonzero leaves observed by the signed
universal machine. -/
noncomputable def nonzeroEquiv : g.NonzeroHistories ≃ NonzeroPath g.machine g.limit.val g.cap.val g.privateClock :=
  g.rawEquivNative.subtypeEquiv (fun z => by rw [g.rawEquivNative_weight z])

/-- Sum of weights over the actual native-equivalent finite set of interior assignments
and complete local event paths. -/
noncomputable def rawValue : ℤ :=
  letI : Fintype g.Paths := Fintype.ofFinite g.Paths
  letI : Fintype g.Histories := Fintype.ofEquiv g.Paths g.rawEquivNative.symm
  ∑ z : g.Histories, z.val.weight

/-- The finite sum over physical interior histories is exactly the paper's native
signed path value on the real initialized input. -/
theorem rawValue_eq_native : g.rawValue = nativeValue g.machine g.limit.val g.cap.val g.privateClock := by
  classical
  let : Fintype g.Paths := Fintype.ofFinite g.Paths
  let : Fintype g.Histories := Fintype.ofEquiv g.Paths g.rawEquivNative.symm
  unfold rawValue nativeValue
  exact Finset.sum_equiv g.rawEquivNative (by simp) (fun z _ => g.rawEquivNative_weight z)

end Setup
end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
