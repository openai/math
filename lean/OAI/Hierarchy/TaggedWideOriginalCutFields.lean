import OAI.Hierarchy.TaggedWideFundedAnchors
import OAI.Hierarchy.TaggedWideOriginalAnchorWords

namespace OAI
/-! # Observing original positive rows in a dense paid gate -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing
open ProtocolRAM ProtocolRAMReportedPorts Tagged.WideStack TaggedShorterGroups
open scoped Classical Fin.CommRing
set_option quotPrecheck false

variable {F : Type*} [Field F] {W : ℕ} (s : Format) (ports lanes : ℕ)
variable (a : Inputs) (old : Fin (s.withSlots ports lanes).N→ProtocolRAMEmit.Row) (before : Memory W)
    (fit : (s.withSlots ports lanes).Limits W old)
    (ins : Leaf.Installed F (s.withSlots ports lanes).groups ports lanes (s.withSlots ports lanes).w (s.withSlots ports lanes).menu (s.withSlots ports lanes).γ old)
variable (active : ∀i,0<pieces old (s.withSlots ports lanes).w i → (a.directory.read before (a.owner.eval before (i.val:Word W))).val=(old i).group)
    (owner : ∀i,0<pieces old (s.withSlots ports lanes).w i → (old i).group<(s.withSlots ports lanes).groups)
    (slots : ∀b (i : ProtocolRAMPackedPlacement.Live old (s.withSlots ports lanes).w),(s.withSlots ports lanes).starts a before b i.val=(ins.port b i.val).val*lanes)
local notation "f" => s.withSlots ports lanes
local notation "group" => fun i : Fin (s.withSlots ports lanes).N=>(a.directory.read before (a.owner.eval before (i.val:Word W))).val

/-- A dense paid gate observes the very field stored by the actual complete format.
Here the output may be the last memory after all later formats and pruning. -/
theorem Format.originalAnchor_observed {U : ℕ} (r : ℕ) (width : U≤2^W)
    (extent : (f).window.stop r≤U) (out : Memory W)
    (stored : ∀q, out ((f).address r q)=
      (s.originalAnchor ports lanes a old before fit ins active owner slots).word old q)
    (q : TaggedShorterScatter.Field (f).window.C (f).D) :
    out (Tagged.WideControlJoin.Gate.denseAddr width
      (frozenRow ((f).window.base r) (((f).scatter_end r).trans extent) q)).val =
      (TaggedShorterScatter.contents ins.bank.counts ins.bank.bound fit.batch fit.idFits ins.bank.place q : Word W) :=
  (stored (.inr q)).trans (s.originalAnchor_field ports lanes a old before fit ins active owner slots q)

end Hierarchy.ProtocolRAMFrozenWindow

end
end OAI
