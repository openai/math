import OAI.Hierarchy.DescentPhysicalResetScene
import OAI.Hierarchy.DescentResetStemProjectedTariff
import OAI.Hierarchy.DescentResetPeerTariff

namespace OAI
/-! Charges for the original evidence, peer detection, and compacted parent publishers. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentDyadicSpan DescentResetStemKey DescentResetStemPackedIssue
open DescentResetPeerUnionRAM DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (ok : v.SceneRoom base s w)
local notation "p" => v.peer
local notation "B" => v.rawTables base
local notation "D" => (p).oldDegree
local notation "M₁" => (p).lanes

def oldEvidenceBill (limit : ℕ) :=
  (4+10*words D v.stemField v.oldLanes)+
    (4+v.oldKeysCount*(4+((p).oldHosts*chunks v.oldGroups v.oldLanes)*(2*(14+(D+2)*(limit+11))+4)))+
    7*Mixed.keyNames D v.stemField v.oldLanes v.oldKeysCount limit+
    (16+10*(B).words)+7*(15*((B).words+4))

theorem oldEvidence_price (limit : ℕ) (cost : ∀q i,(s.evidence.source q i).work ≤ limit) :
    (v.originalPhase base s ok).ticks+7*names (v.originalPhase base s ok).program ≤ v.oldEvidenceBill base limit := by
  let e:=s.evidence
  have ticks:=Columns.clock_bound e.decode e.sides e.source base v.oldLanes (p).oldHosts v.oldGroups limit cost
  have key : names (Columns.code e.decode e.sides e.source base v.oldLanes (p).oldHosts v.oldGroups w)≤
        Mixed.keyNames D v.stemField v.oldLanes v.oldKeysCount limit := by
    rw [Columns.code,names_seq]
    have rom : names (DescentResetStemKey.program e.decode v.oldLanes w base)=15*(words D v.stemField v.oldLanes+1) :=
      DescentPackedZip.Book.names (gates e.decode) (unit D v.stemField) v.oldLanes w base
    rw [rom]
    apply Nat.add_le_add_left
    apply (ProbeStage.Native.columns_text _ _ _ (14+(D+2)*(limit+11)) _ ?_).trans
    · simp only [Columns.terms,List.length_ofFn,le_refl]
    · intro x hx
      obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hx
      exact expr_work e.decode v.oldLanes base (e.sides q) (e.source q) limit (cost q)
  have seen:=RawTables.any e.board e.rootBits e.depth (B) e.template (fun _=>0:Memory w)
    ((v.tables_end base ok.sameLanes).trans_lt ok.evidenceFit)
  change _+7*names (v.originalEvidence e base w)≤_
  unfold originalEvidence
  rw [names_seq,seen.2.2.1]
  dsimp only [originalPhase,evidenceClock,RawTables.Layout.ticks,oldEvidenceBill,e] at *
  omega

def peerBill (limit : ℕ) :=
  let old:=Program.timeBound (p).oldHosts (p).shapes D (p).evidence (p).bits (p).evidenceLanes (p).evidenceGroups limit
  let oldNames:=Program.hardwareBound (p).oldHosts (p).shapes D (p).evidence (p).bits (p).evidenceLanes (p).evidenceGroups limit
  let H:=(p).hosts
  let loc:=3*DescentResetSelfPortsRAM.pad H
  let chart:=DescentScalarHaloPortROM.length H (p).groups M₁ 4
  (old+((4+10*loc)+(4+10*chart)+(4+(H*4)*84)+(4+(H*4)*25004))+(4+10*(3*H)))+
    7*(oldNames+(15*(loc+1)+15*(chart+1)+171+50011)+15*(3*H+1))

theorem peer_price (limit : ℕ) (cost : ∀e c,(s.peers.src e c).work ≤ limit) :
    (v.triplePhase base s ok).ticks+7*names (v.triplePhase base s ok).program ≤ v.peerBill limit := by
  let z:=v.peers base
  let u:=s.peers
  have prior:=Program.prices z (p).oldHosts (p).shapes D (p).bits (p).evidenceLanes (p).evidenceGroups w
    u.old u.test u.src limit cost
  have self:=DescentResetSelfPortsRAM.tariff ((p).rawPeers z) ((p).three z) (p).hosts (p).groups M₁ w
  have palette:names (DescentResetTrunkPalette.program u.board u.rootBits u.depth w ((p).threshold z) (p).oldHosts)=
      15*(3*(p).hosts+1) := by
    unfold DescentResetTrunkPalette.program
    rw [names_mount,u.palette]
    rfl
  change (p).ticks u z+7*names ((p).program u z w)≤_
  unfold PeerAperture.ticks PeerAperture.program
  rw [names_seq,names_seq,palette]
  dsimp only [peerBill] at *
  omega

def stemBill (T U : ℕ) :=
  260*(1+(p).hosts+v.newHosts)+7*(15*((p).hosts+1)+2048)+
    Mixed.Projected.bill D v.stemField v.metaBits v.oldTicketCount (p).oldHosts v.newHosts (p).groups
      v.blocks v.oldLanes M₁ v.signedQueries T U

theorem stem_price (T U : ℕ) (operands : ∀q j,(s.stems.operands q j).work≤T)
    (ports : s.stems.ports.All (fun e=>e.work≤U)) (old : 0 < v.oldLanes) :
    (v.parentStemPhase base s ok).ticks+7*names (v.parentStemPhase base s ok).program ≤ v.stemBill T U := by
  let room:=(v.front_order base).2.1.trans_lt ok.stems.final
  have time:=DescentResetParentDate.invoice (v.parentStart base) (p).hosts v.newHosts s.stems.flags room
  have text:=DescentResetParentDate.hardware (v.parentStart base) (p).hosts v.newHosts (p).shapes s.stems.flags room
  have projected:=Mixed.Projected.tariff (v.parentEnd base) (v.parent base).base v.metaBits
    (p).oldHosts v.newHosts (p).groups v.blocks v.oldLanes M₁ w s.stems.parse s.stems.side s.stems.operands
    s.stems.ports T U operands ports old ok.stems.blocks ok.stems.positive
  change v.stemTime s.stems base w ok.stems+7*names (v.stemFront s.stems base w ok.stems)≤_
  simp only [stemFront,stemTime,names_seq,stemBill]
  omega

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
