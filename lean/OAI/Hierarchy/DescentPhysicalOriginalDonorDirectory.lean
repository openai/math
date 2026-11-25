import OAI.Hierarchy.DescentPhysicalPublicOriginalFrame
import OAI.Hierarchy.DescentResetPublicCuts
import OAI.Hierarchy.DescentOriginalDonorDenseRead
import OAI.Hierarchy.DescentPhysicalNamedOriginals
import OAI.Hierarchy.DescentResetOriginalNumberRoom

namespace OAI
/-! Authentic compact actor and inverse coordinates at the completed original donor publication. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentSixParty.Chronology
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w) (ok : u.Ready) (m : Memory w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "ss" => (v).sheets
local notation "R" => (v).remap b
local notation "r" => (R).endAddress
local notation "actor" => (v).actorEnd b
local notation "dir" => (v).actor.directory ((v).middle.stop b)
local notation "O" => (v).issuedScene b u.earlier
local notation "start" => u.masked.image (u.privateResult m)
local notation "pre" => u.numbered.prefixOutput r start
local notation "pub" => u.numbered.publicSide r
include ok

theorem donor_prefix_relay (z : ℕ) (hz : z<r) :
    pre z=(R).mounted (u.privateResult m) z :=by
  have order : r≤(ss).metaEnd r:=u.masked.mixed.ordered.1.trans u.masked.mixed.ordered.2
  have before:=u.numbered.prefix_any r start ok.numbers.donor
  have masked:=u.masked.mixed.any (u.masked.relay.mounted (u.privateResult m))
    (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  exact (before.2.2 z (.inl (hz.trans_le order))).trans (masked.2.2 z (.inl hz))

theorem donor_prefix_books : (R).Books pre :=by
  have loaded:=(R).books (u.privateResult m)
  have rows : (R).hosts*(R).parts≤(R).pitch:=Nat.le_pow_clog (by decide) _
  have sparse : (R).sparse≤(R).rawPitch:=Nat.le_pow_clog (by decide) _
  have «prefix»:=u.donor_prefix_relay ok m
  constructor
  · intro host j
    rw [«prefix» _ ?_]
    · exact loaded.host host j
    · have lt:=(finProdFinEquiv (host,j)).isLt.trans_le rows
      change (R).first+_<(R).first+(2*(R).pitch+(R).rawPitch);omega
  · intro host j
    rw [«prefix» _ ?_]
    · exact loaded.low host j
    · have lt:=(finProdFinEquiv (host,j)).isLt.trans_le rows
      change (R).first+(R).pitch+_<(R).first+(2*(R).pitch+(R).rawPitch);omega
  · intro j
    rw [«prefix» _ ?_]
    · exact loaded.stride j
    · have lt:=j.isLt.trans_le sparse
      change (R).first+2*(R).pitch+_<(R).first+(2*(R).pitch+(R).rawPitch);omega

theorem donor_prefix_actors (z : ℕ) (hz : z<actor) : pre z=m z :=by
  have cuts:=(v).cuts b
  have trunk:=hz.trans_le cuts.trunk
  have early : z<u.masked.first:=trunk.trans_le (cuts.mass.trans (cuts.joint.trans cuts.privateEnd))
  have relay : z<r:=early.trans_le u.masked.ordered.1
  have order : r≤(ss).inputDonorsEnd r:=
    (u.masked.mixed.ordered.1.trans u.masked.mixed.ordered.2).trans ((ss).number_cuts r).1
  have step:=(pub).any ok.numbers.public_ pre
  exact ((step.2.2 z (.inl (relay.trans_le order))).symm.trans (u.public_original_scene ok m z trunk)).trans
    (((v).front.trunkScene_any actor O u.sceneFits m ok.trunk).2 z (.inl hz))

theorem donor_prefix_directory {used : ℕ} (name : Fin used→Fin (v).front.peer.hosts)
    (count : m (dir).count.base=(used:Word w))
    (inverse : ∀i:Fin used,m ((dir).inverse.base+i.val)=((name i).val:Word w))
    (countFits : used<2^w) (hostFits : (ss).hosts≤2^w) (size : used≤(dir).inverse.size) :
    ((v).originalDonorLayout u.numbered.signedSlots).Directory (H:=(ss).hosts) name pre (R).first
      (dir).count (dir).inverse r :=by
  have fits:=(dir).fits (((v).cuts b).trunk.trans_lt ok.trunk)
  have cnt:=(fits.2.2.2.1)
  have inv:=(fits.2.2.2.2)
  have cuts:=(v).cuts b
  have start₀ : actor≤(R).first:=cuts.trunk.trans (cuts.mass.trans (cuts.joint.trans cuts.privateEnd))
  have later {bank : Bank} (p : bank.Fits w actor) : bank.Fits w (R).first :=
    ⟨p.1,p.2.1,p.2.2.trans start₀⟩
  have room : r<2^w:=u.masked.ordered.2.trans_lt ok.masked
  refine ⟨u.donor_prefix_books ok m,(R).book_fits (dir).count (dir).inverse (later cnt) (later inv) room,
    ?_,?_,countFits,hostFits,size⟩
  · exact (u.donor_prefix_actors ok m _ ((Nat.lt_add_of_pos_right cnt.1).trans_le cnt.2.2)).trans count
  · intro i
    exact (u.donor_prefix_actors ok m _ ((Nat.add_lt_add_left (i.isLt.trans_le size) _).trans_le inv.2.2)).trans (inverse i)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
