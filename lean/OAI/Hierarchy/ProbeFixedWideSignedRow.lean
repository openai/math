import OAI.Hierarchy.TaggedWideCalendarDateRow
import OAI.Hierarchy.ProbeFixedWideSpillDates

namespace OAI
/-! # The selected signed circuit on a corrected native attempt page -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ThreeFlat Routing
open Tagged Tagged.WideControlJoin Tagged.WideStack AdaptiveProbe ProbeStage
open WireTelescope WireTelescope.PassMatrix WireTelescope.PassMatrix.PartyPins
open WideCPU Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {F Ex Sel Data : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype Data]
    {k : ℕ} {p q Q σ Λ : ℝ}

def signedRowCandidate
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width unitCost : ℕ) (a : Attempt) (G : Gate)
    {T : ℕ} (g : Dated T) (work : ℕ) (j : Fin T) (s : Fin g.sites)
    (words : Bool → Fin v.widePacketDegree → Fin (v.wideNeighborCap width unitCost) →
      SitePins Ex Sel Data G ⊕ Bool)
    (inside : ∀ f : SiteControls.Field v.widePacketDegree, controlAddress g work j s f < G.u)
    (readBits : v.wideNeighborDigits width unitCost ≤ G.W+1)
    (atom : Fin (v.signedPartyCount h a)) : BitNetwork F (Fintype.card (SitePins Ex Sel Data G)) :=
  let read := ballotWord (Ex:=Ex) (Sel:=Sel) (D:=Data) G g work j s
  let packet : BitNetwork F (Fintype.card
      (Gathered (SitePins Ex Sel Data G) v.widePacketDegree (v.wideNeighborCap width unitCost))) :=
    v.signedParty (V:=SitePins Ex Sel Data G) h width a (v.wideNeighborCap width unitCost)
      (v.partyRoleBits h) (v.partyLaneBits h width a unitCost) v.partyKeyBits read atom
  spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) (deg:=v.widePacketDegree)
    (width:=v.wideNeighborCap width unitCost) (bits:=v.wideNeighborDigits width unitCost)
    G g work j s inside words readBits packet

/-- Vacant sites carry exactly their unused wires. At an occupied site, the
stored ballot word chooses a packet and its party using the native order. -/
def signedRow
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width unitCost : ℕ) (a : Attempt) (G : Gate)
    {T : ℕ} (g : Dated T) (work : ℕ) (j : Fin T) (s : Fin g.sites)
    (words : Bool → Fin v.widePacketDegree → Fin (v.wideNeighborCap width unitCost) →
      SitePins Ex Sel Data G ⊕ Bool)
    (inside : ∀ f : SiteControls.Field v.widePacketDegree, controlAddress g work j s f < G.u)
    (modeAddress : ballotAddress g work j s 0 < G.u)
    {tagBits : ℕ} (tagsFit : v.signedPartyCount h a + 1 ≤ 2^tagBits) (tagsRead : tagBits ≤ G.W+1)
    (readBits : v.wideNeighborDigits width unitCost ≤ G.W+1) :
    BitNetwork F (Fintype.card (SitePins Ex Sel Data G)) :=
  datedProgram (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) (deg:=v.widePacketDegree)
    (width:=v.wideNeighborCap width unitCost) G g work j s tagsFit words modeAddress tagsRead
    (v.signedRowCandidate h width unitCost a G g work j s words inside readBits)

theorem signedRow_fee
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width unitCost : ℕ) (a : Attempt) (G : Gate)
    {T : ℕ} (g : Dated T) (work : ℕ) (j : Fin T) (s : Fin g.sites)
    (words : Bool → Fin v.widePacketDegree → Fin (v.wideNeighborCap width unitCost) →
      SitePins Ex Sel Data G ⊕ Bool)
    (inside : ∀ f : SiteControls.Field v.widePacketDegree, controlAddress g work j s f < G.u)
    (modeAddress : ballotAddress g work j s 0 < G.u)
    {tagBits : ℕ} (tagsFit : v.signedPartyCount h a + 1 ≤ 2^tagBits) (tagsRead : tagBits ≤ G.W+1)
    (readBits : v.wideNeighborDigits width unitCost ≤ G.W+1) :
    let cost := fun atom : Fin (v.signedPartyCount h a) =>
      v.signedParty (V:=SitePins Ex Sel Data G) h width a (v.wideNeighborCap width unitCost)
        (v.partyRoleBits h) (v.partyLaneBits h width a unitCost) v.partyKeyBits
        (ballotWord (Ex:=Ex) (Sel:=Sel) (D:=Data) G g work j s) atom
    let gather := v.widePacketDegree * v.wideNeighborCap width unitCost +
      v.widePacketDegree * (v.wideNeighborCap width unitCost * (200 * v.wideNeighborDigits width unitCost + 65)) +
      v.widePacketDegree * v.widePacketDegree *
        (2308 * v.wideNeighborCap width unitCost * (Nat.log2 (v.wideNeighborCap width unitCost) + 2))
    let row := v.signedRow h width unitCost a G g work j s words inside modeAddress tagsFit tagsRead readBits
    row.cells + row.internal ≤ v.widePacketDegree * v.widePacketDegree *
      (2308 * v.wideNeighborCap width unitCost * (Nat.log2 (v.wideNeighborCap width unitCost) + 2)) +
      177^tagBits * ∑ atom : Fin (v.signedPartyCount h a), (2*gather + ((cost atom).cells + (cost atom).internal)) := by
  intro cost gather row
  refine (datedProgram_bill (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) (deg:=v.widePacketDegree)
    (width:=v.wideNeighborCap width unitCost) G g work j s tagsFit words modeAddress tagsRead
    (v.signedRowCandidate h width unitCost a G g work j s words inside readBits)).trans ?_
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro atom _
  exact spillGather_cost (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=Data) (deg:=v.widePacketDegree)
    (width:=v.wideNeighborCap width unitCost) (bits:=v.wideNeighborDigits width unitCost)
    G g work j s inside words readBits (cost atom)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
