import OAI.Hierarchy.DescentResetParentDirectoryRead
import OAI.Hierarchy.DescentPhysicalResetStemEntry
import OAI.Hierarchy.DescentPhysicalResetTrunkScene

namespace OAI
/-! # The actual compact parent IDs of the relocated reset packets -/
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

def packetOwner {pad : ℕ} (v : Fin pad) : Fin H :=
  if real:v.val<Fintype.card Vnew then Z.parentIndex T vertex ⟨v.val,real⟩ else ⟨0,pos⟩

theorem issued_parent_rows {w pad : ℕ} (capacity : Fintype.card Vnew≤pad) (base : ℕ)
    (flags : Bank) (mem : Memory w) (old : flags.Fits w base) (rows : H*shapes≤flags.size)
    (room : DescentResetParentDate.endAddress base (H*shapes) pad<2^w)
    (bitmap : ∀j:Fin (H*shapes),mem (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(raw v).val) j.val:Word w)) :
    DescentResetStemKeyReindex.Directory (parent base (H*shapes) pad).base
      (Z.packetOwner T vertex pos (pad:=pad)) (DescentResetParentDate.memory base (H*shapes) pad shapes flags mem room) := by
  obtain ⟨real,ghost,_⟩:=Z.bounded_parent_directory T vertex capacity base flags mem old rows room bitmap
  intro v
  by_cases hits:v.val<Fintype.card Vnew
  · simpa only [packetOwner,dite_eq_left hits] using real ⟨v.val,hits⟩
  · rw [packetOwner,dite_eq_right hits]
    exact ghost v (by
      rintro ⟨j,eqn⟩
      apply hits
      rw [←congrArg Fin.val eqn]
      exact (Z.denseHostRank T vertex j).isLt)

open DescentDatedAddressBook in
theorem trunk_packet_parent {w : ℕ} (v : CandidateFront) (base : ℕ) (scene : v.Scene)
    (space : v.SceneRoom base scene w) (mem : Memory w) (capacity : Fintype.card Vnew≤v.newHosts)
    (population : v.peer.hosts=H*shapes) (kinds : v.peer.shapes=shapes)
    (old : scene.stems.flags.Fits w (v.parentStart base)) (rows : H*shapes≤ scene.stems.flags.size)
    (room : v.trunkEnd base<2^w)
    (bitmap : ∀j:Fin (H*shapes),v.preParent base scene space mem (scene.stems.flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun u=>(raw u).val) j.val:Word w)) :
    DescentResetStemKeyReindex.Directory (v.parent base).base (Z.packetOwner T vertex pos (pad:=v.newHosts))
      ((v.trunkScene base scene space).image mem) := by
  have maxed:=v.front_order base
  have small : DescentResetParentDate.endAddress (v.parentStart base) (H*shapes) v.newHosts<2^w:=by
    rw [←population]
    exact maxed.2.1.trans_lt space.stems.final
  have data:=Z.issued_parent_rows T vertex pos capacity (v.parentStart base) scene.stems.flags
    (v.preParent base scene space mem) old rows small bitmap
  intro j
  have h₀ : (v.parent base).base+j.val<v.parentEnd base :=
    (Nat.add_lt_add_left (j.isLt.trans_le (Nat.le_pow_clog (by decide) _)) _).trans_le maxed.2.2
  rw [v.trunkScene_before base scene space mem room _ (h₀.trans_le maxed.2.1),v.entry_word base scene space mem _ h₀]
  unfold CandidateFront.stemEntry CandidateFront.parent
  simpa only [population,kinds] using data j

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
