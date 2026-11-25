import OAI.Hierarchy.TaggedWideSitePublisher
import OAI.Hierarchy.TaggedWideActiveBits
import OAI.Hierarchy.ProbeAwayPartyBits

namespace OAI
/-! # Actual participant and finite signed branch at a permanent spatial site -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteScatter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing Diagonal TraceWords
open scoped Classical Fin.CommRing

variable {W C sites formats digits : ℕ} {A V : Type} (place : A ↪ Fin sites) (kind : A→Fin formats)

def tag (room : formats+1≤2^digits) : Fin (formats+1) ↪ (Fin digits→Bool) where
  toFun k:=bits (k.castLE room)
  inj' _ _ eqn:=Fin.ext (congrArg (fun i : Fin (2^digits) => i.val) (bits_injective eqn))

def selected (s : Fin sites) : Fin (formats+1) := (foundAt place s).elim 0 (fun a=>(kind a).succ)

theorem mode_bits (word : A→Fin C→Word W) (header : Fin C)
    (raw : ∀a,(word a header).val=(kind a).val+1) (fit : formats+1≤2^digits) (s : Fin sites)
    (read : Fin digits→V) (v : V→Bool)
    (native : ∀j,v (read j)=(table place word s header).val.testBit j.val) :
    v ∘ read=tag fit (selected place kind s) := by
  funext j
  rw [Function.comp_apply,native]
  by_cases hit : s∈Set.range place
  · obtain ⟨a,rfl⟩ := hit
    rw [active,raw]
    simp only [selected,found_live,Option.elim_some]
    rfl
  · rw [idle _ _ _ _ hit]
    simp only [selected,found_idle _ _ hit,Option.elim_none]
    rfl

end Hierarchy.ProtocolRAM.SiteScatter

namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open CalendarTape AdaptiveProbe Probe
open scoped Classical BigOperators

theorem Placed.wants_away {F : Type} [Field F] {S : ℕ} (P : Placed F S) (r : ℕ)
    {s : Fin S} (away : s∉Set.range P.place) : Subsingleton (State (P.wants r) s) := by
  let : Nonempty (Fin P.sites) := ⟨P.root⟩
  let : Nonempty (Fin S) := ⟨P.place P.root⟩
  have input : placeWidths P.place (P.data.inputWidths r)=P.wants r :=
    physical_demand (edge:=P.edge) (req:=P.wanted) P.place P.data.width r
  rw [←input]
  exact PhysicalMatrix.state_away P.place (P.data.inputWidths r) away

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
