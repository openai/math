import OAI.Hierarchy.DescentContactMaskRanks
import OAI.Hierarchy.DescentContactSelfRanks
import OAI.Hierarchy.DescentPrivateRankRequests

namespace OAI
/-! The three ranked private mask fields on an actual inherited five-field root page. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentPackedZip DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster DescentResetPeerJointRAM
open DescentCommonHost DescentResetWindowResidentSources DescentDatedAddressBook DescentResetLocalRoster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8000
set_option maxHeartbeats 1800000
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {O bw H : ℕ} (pad : Fintype.card input.V≤O) (live : used≤H)
local notation "host" => input.vertex.trans (Fin.castLEEmb pad)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B pad
local notation "names" => compactActorName B pad
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "P₀" => O*width

variable {date : PhysicalReset} {floor : ℕ} {I : date.DateInputs floor bw} {N : ℕ}
  (board : I.CandidateChannels) (name : Fin N→Fin I.masked.sparseHosts)
  (base : ℕ) (src : DescentResetPeerJointRAM.Sources) (m : Memory bw)
  (rows : Fin P₀→Fin 4→Option (Fin P₀)) (room : DescentResetPeerJointRAM.Room src base H P₀ O (A).degree bw)
  (stored : DescentResetPeerJointRAM.Reads src used names (indexed rows) adj m)
  (jointRoom : width*radix (A).degree≤2^bw)
  (small : 4≤2^I.masked.field)
  (u : Host) (v₀ : Fin I.masked.hosts) (g₀ : Fin I.masked.groups)
  (roster : present rows (raw u.1.2)=(insert u.1.2 (B.next.placement.near u.1.2)).map raw)
  (peer : ∀s,(board.peer s v₀ g₀).val=DescentResetPeerJointRAM.value O width (A).degree adj used names (indexed rows) ((dense u.1.2).castLE live) s)

open DescentPackedPrivateMenu DescentResetPeerUnionRAM
local notation "V₀" => date.successor
local notation "Q₀" => (V₀).privateShape
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(Ht+1))
local notation "loc" => ((dense u.1.2).castLE live)
local notation "oldRoot" => (receiverRoot B u).1
variable {field keyBits count : ℕ} (prior : PriorPeerWords B O field keyBits)
    (unit : 0<(Z).unit) (panels : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel Ht count)
    (issued : PeerOrigins B pad prior unit panels) (oldBatch batch : ℕ)

include room stored jointRoom small roster peer issued in
theorem private_mask_ranks (job : ℕ) (x : Fin (Q₀).blocks) (q : Fin (Q₀).keys)
    (sector : (V₀).jobAt job=some (.inr (x,q))) (s : Bool) (t : (Z).RootTicket T) (l : Fin cap₀)
    (area : width≤2^I.masked.field) (mass : B.next.placement.cap<2^I.masked.field)
    (fit : width*radix (A).degree≤2^I.masked.field) (degree : (V₀).front.peer.oldDegree=(A).degree)
    (sparse : ∀j : Fin 3,(DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.privateFields x q j) v₀ g₀).val=
      (privateDigit B pad prior oldBatch batch I.masked.field u s t l j).val)
    (near : Fin P₀→Fin 3→Option (Fin P₀))
    (aux : ∀j : Fin 4,(board.aux j v₀ g₀).val=DescentResetPeerJointPacked.Aux.value width names adj near loc j)
    (a : DescentParallelBase.Local (blocks B) u) (found : localOrigin B u (privateShelfIndex B (localPrivateId _ _ cap₀ (s,t,l)))=some a) :
    (board.maskValues name job v₀ g₀ 4).val=localClass B u ((blocks B).src a.val) ∧
    (board.maskValues name job v₀ g₀ 5).val=localClass B u ((blocks B).dst a.val) ∧
    (board.maskValues name job v₀ g₀ 6).val=localClass B u u:=by
  obtain ⟨left,right,atLeft,atRight,_,_⟩:=private_rank_requests B pad prior unit panels issued oldBatch batch
    I.masked.field u s t l a found area mass
  have srcShape:=(sparse 0).trans left
  have dstShape:=(sparse 1).trans right
  obtain ⟨selfHalo,selfName⟩:=current_self_words B pad live near u
  have self0:=(aux 0).trans selfHalo
  have self1:=(aux 1).trans selfName
  have own : oldRoot∈originDomain B u:=Finset.mem_insert_self ..
  have narrow (v : Host) : jointNumber B u oldRoot (relativeShape B v)<2^I.masked.field:=by
    have bit:=halo_radix B u oldRoot own
    have sh : relativeShape B v<width:=((Z).hostFields T vertex v.1.2).2.isLt
    exact (Nat.add_lt_add_left bit _).trans_le (by rw [←Nat.mul_succ];exact (Nat.mul_le_mul_left _ sh).trans (by simpa only [DescentResetPeerJointRAM.radix, Nat.mul_comm] using fit))
  apply mask_ranks_local B pad live board name base src m rows room stored jointRoom small u v₀ g₀ roster peer job a
  · rwa [atLeft]
  · rwa [atRight]
  · simp only [PhysicalReset.DateInputs.CandidateChannels.endpoint,sector,PhysicalReset.DateInputs.CandidateChannels.joint,
      show (0:Fin 3).val<2 by decide,ite_true,srcShape,self0,degree,atLeft]
    exact Fin.val_cast_of_lt (narrow _)
  · simp only [PhysicalReset.DateInputs.CandidateChannels.endpoint,sector,PhysicalReset.DateInputs.CandidateChannels.joint,
      show (1:Fin 3).val<2 by decide,ite_true,dstShape,self0,degree,atRight]
    exact Fin.val_cast_of_lt (narrow _)
  · simpa only [PhysicalReset.DateInputs.CandidateChannels.endpoint,sector,PhysicalReset.DateInputs.CandidateChannels.joint,
      show ¬(2:Fin 3).val<2 by decide,ite_false] using self1

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
