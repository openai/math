import OAI.Hierarchy.DescentDatedPacketParent

namespace OAI
/-! # Parent identifiers from the compact bitmap written by the named actor directory -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentResetParentAperture DescentHubBits
open DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {world : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput world price ε h C Ht) (T : Z.Terminals)
variable {H : ℕ} (vertex : Z.V↪Fin H) (pos : 0<H)
local notation "Vnew" => ↥(commonNames Z T)
local notation "shapes" => (roster Z.graph (Z.k-T.commonDepth) Ht).card
local notation "raw" => rawHostRank Z T vertex

open DescentDatedAddressBook in
theorem trunk_parent_from_flags {w : ℕ} (v : CandidateFront) (base : ℕ) (scene : v.Scene)
    (space : v.SceneRoom base scene w) (loaded : Memory w) (capacity : Fintype.card Vnew≤v.newHosts)
    (population : v.peer.hosts=H*shapes) (kinds : v.peer.shapes=shapes)
    (old : scene.stems.flags.Fits w (v.parentStart base)) (rows : H*shapes≤ scene.stems.flags.size)
    (low : scene.stems.flags.base+H*shapes≤base) (room : v.trunkEnd base<2^w)
    (flags : ∀j:Fin (H*shapes),loaded (scene.stems.flags.base+j.val)=
      if ∃i:Vnew,raw i=j then 1 else 0) :
    DescentResetStemKeyReindex.Directory (v.parent base).base (Z.packetOwner T vertex pos (pad:=v.newHosts))
      ((v.trunkScene base scene space).image loaded) := by
  apply Z.trunk_packet_parent T vertex pos v base scene space loaded capacity population kinds old rows room
  intro j
  rw [v.parent_prior base scene space loaded _ (by have hj:=j.isLt;omega),flags]
  by_cases hit : ∃i:Vnew,raw i=j
  · obtain ⟨i,rfl⟩:=hit
    have present := DescentEdgeTapePrefix.row_present (fun _ : Vnew => 1)
      (fun u : Vnew => (raw u).val) (Fin.val_injective.comp (raw).injective) i
    simp [present]
  · simp [hit,DescentEdgeTapePrefix.row_absent _ _ _ (fun i e=>hit ⟨i,Fin.ext e⟩)]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
