import OAI.Hierarchy.DescentPhysicalResetTrunkScene
import OAI.Hierarchy.DescentPhysicalResetStemChart
import OAI.Hierarchy.DescentResetPeerPublicTerms
import OAI.Hierarchy.DescentDatedActorAperture
import OAI.Hierarchy.DescentDatedResetOutput
import OAI.Hierarchy.DescentContactDonorMarkers

namespace OAI
/-! # Public reset operands from the actual actor directory, paid roots, and earlier signed banks -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup DescentResetLocalRoster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

namespace CandidateFront
variable (v : CandidateFront) (floor : ℕ)
local notation "P" => v.peer
local notation "C" => v.contactLayout floor
local notation "L" => v.rawTables floor

structure ProbeShape (e : v.Evidence) : Prop where
  count : (P).evidence=Axes.rows (C).donors (C).sockets (PeerCatalog.privateAxis L C)
  chunks : chunks (P).evidenceGroups (P).evidenceLanes=chunks (C).groups (C).batch
  keys : (C).donors≤v.oldKeysCount
  nodes : e.n=(C).n
  palette : (DescentDenseHostOrder.roster e.board e.rootBits e.depth).card=(P).shapes

/-- Each stem is addressed in the key bank issued before the private and contact programs. -/
def originalPages (pages : Bool→Root (C).residual (2^(C).n)→Bank) (starts data : Bank) : PeerCatalog.Banks C :=
  ⟨fun j=>DescentResetStemKey.Columns.bank floor (P).oldDegree v.stemField v.oldLanes
    (P).oldHosts v.oldGroups j.val,pages,starts,data⟩

variable (e : v.Evidence) (shape : v.ProbeShape floor e)
def compiledPeers (pages : Bool→Root (C).residual (2^(C).n)→Bank) (starts data old : Bank) :
    (P).Inputs where
  old := old
  test := marked
  src i j := (PeerCatalog.terms L C (v.originalPages floor pages starts data)).all (i.cast shape.count)
    (j.cast shape.chunks)
  n := e.n
  h := e.oldPorts
  rootBits := e.rootBits
  depth := e.depth
  board := e.board
  palette := shape.palette

include shape in
theorem issued_key_fits {w : ℕ} (pages : Bool→Root (C).residual (2^(C).n)→Bank) (starts data : Bank)
    (j : Fin (C).donors) (space : v.oldKeys floor<2^w) :
    ((v.originalPages floor pages starts data).keys j).Fits w (v.oldKeys floor) :=
  (DescentResetStemKey.Columns.bank_fits floor (P).oldDegree v.stemField v.oldLanes (P).oldHosts v.oldGroups
    v.oldKeysCount w (j.castLE shape.keys) space).1

def signedTemplate (j : Fin (2*v.oldTicketCount)) :=
  let item : Fin 2 × Fin v.oldTicketCount :=finProdFinEquiv.symm j
  e.template (finTwoEquiv item.1) item.2
structure Originals where
  evidence : v.Evidence
  shape : v.ProbeShape floor evidence
  pages : Bool→Root (C).residual (2^(C).n)→Bank
  actorStarts : Bank
  actorData : Bank
  oldRoster : Bank
  oldHub : Bank
  sameBoard : (C).oldFields=DescentRotorWindowArchive.count v.donor.degree v.donor.lows v.donor.cap
  originalDonors : DescentContactSenderDate.Prior v.donor.degree v.donor.lows v.donor.cap v.donor.n v.donor.residual
  sameDonors : (C).half=v.donor.lows*(2*v.donor.cap)
  signs : Fin v.signedQueries→Bool
  operands : Fin v.signedQueries→Fin ((P).oldDegree+2)→Expr
  queries : v.projectionCount=v.signedQueries*((P).oldDegree+2)
  field : v.projectionBits=v.stemField

def fromOriginals (base : ℕ) (old : v.Originals base) (flags count inverse : Bank) : v.Scene where
  evidence := old.evidence
  rotorPorts := old.evidence.oldPorts
  rotor := old.shape.nodes ▸ old.evidence.board
  boardReads i := v.donor.oldBoard old.originalDonors (i.cast old.sameBoard)
  donor := old.originalDonors
  donorSlots := old.sameDonors
  peers := v.compiledPeers base old.evidence old.shape old.pages old.actorStarts old.actorData old.oldRoster
  count := count
  inverse := inverse
  rawHeader := DescentSixParty.ClosedReset.Window.rawTrunkExpr v.metaBits v.peer.hosts
    (v.peer.rawPeers (v.peers base)) (v.peer.threshold (v.peers base))
  stems := {
    flags := flags
    parse := old.evidence.decode
    side := old.signs
    operands := old.operands
    ports := DescentResetStemMaskedPorts.ports ⟨inverse,v.parent base,v.rawNeighborBank base,old.oldHub⟩ count v.peer.oldHosts
      (v.signedTemplate old.evidence)
    queries := old.queries
    digits := old.field }

end CandidateFront

namespace ResetOutput
variable (v : ResetOutput) (base : ℕ)
local notation "F₀" => v.front
local notation "start₀" => v.actorEnd base
local notation "P₀" => (F₀).peer
local notation "C₀" => (F₀).contactLayout start₀
local notation "dir₀" => v.actor.directory (v.middle.stop base)

abbrev OriginalOperands := (F₀).Originals start₀

variable (old : v.OriginalOperands base)
def issuedRegisters : DescentResetStemTemplatePorts.Banks :=
  ⟨(dir₀).inverse,(F₀).parent start₀,(F₀).rawNeighborBank start₀,old.oldHub⟩

def issuedScene : (F₀).Scene :=
  (F₀).fromOriginals start₀ old (dir₀).flags (dir₀).count (dir₀).inverse

theorem issued_actor_banks :
    let s:=v.issuedScene base old
    s.count=(dir₀).count ∧ s.inverse=(dir₀).inverse ∧ s.stems.flags=(dir₀).flags ∧
      (F₀).stemRegisters start₀ s old.oldHub=v.issuedRegisters base old := ⟨rfl,rfl,rfl,rfl⟩

theorem issued_trunk_prefix (hosts : (dir₀).sites=(P₀).hosts) :
    ((F₀).trunkBanks start₀ (v.issuedScene base old)).number.base=(dir₀).ranks.base := by
  change ((dir₀).ranks.base+(dir₀).sites)-(P₀).hosts=(dir₀).ranks.base
  rw [hosts]
  omega

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
