import OAI.Hierarchy.DescentDatedOriginalHeaders

namespace OAI
/-! # The original, previous, and newborn headers on one physical operand-preparation execution -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace HeaderWords
def reindex {D k K c H G b n q c' H' G' b' : ℕ}
    (cap : c=c') (host : H=H') (groups : G=G') (bits : b=b')
    (x : ScalarOperand.Values D k K c H G b n q) : ScalarOperand.Values D k K c' H' G' b' n q :=
  cap ▸ host ▸ groups ▸ bits ▸ x

theorem reindex_measured {D k K c H G b n q c' H' G' b' N M base w : ℕ}
    (cap : c=c') (host : H=H') (groups : G=G') (bits : b=b')
    (C : Refs D k K c) (x : ScalarOperand.Values D k K c H G b n q) (m : Memory w)
    (obs : Measured C x N M base m) :
    Measured (cap ▸ C) (reindex cap host groups bits x) N M base m:=by
  cases cap;cases host;cases groups;cases bits;exact obs
end HeaderWords

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "rc₀" => v.resolver
local notation "vx₀" => v.vector
local notation "bn₀" => v.bornBook
local notation "g₀" => v.ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "mouth₀" => v.mouthChart mat.newBlocks
local notation "vecAt" => v.vectorStart floor
local notation "routeAt" => v.routedStart floor
local notation "portAt" => v.originPortEnd floor
local notation "mouthEnd₀" => v.originMouthEnd floor
local notation "headerStart" => v.operandOldHeaderStart floor
local notation "headerEnd" => v.operandHeaderEnd floor

local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "ps₀" => v.operandPathStart floor
local notation "refs₀" => (A.directory v floor mat).refs
local notation "Val₀" => References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes
  v.reference.capacity ((rc₀).size+2)
def headerMouthPage (arg : Fin (bn₀).args) : Fin (vx₀).pageCount :=
  finProdFinEquiv ((0:Fin 7),arg.cast mat.newArgs)

def headerMouthRows {nb mb : ℕ} (rows : Val₀ nb mb)
    (home : (bn₀).hosts=(vx₀).hosts) (group : (bn₀).groups=(vx₀).groups*(vx₀).radix)
    (word : (bn₀).bits=(rc₀).size+2) (arg : Fin (bn₀).args) (low : Fin (vx₀).lows) :
    (mouth₀).Val nb mb :=
  HeaderWords.reindex mat.newCap.symm home.symm group.symm word.symm (rows (v.headerMouthPage floor A mat arg) low)

theorem registered_headers {w nb mb} (pg : Fin (vx₀).pageCount)
    (chip : Fin (bn₀).hosts→Fin (bn₀).groups→Cell (bn₀).chipBits)
    (oldBooks : Val₀ nb mb)
    (m : Memory w) (good : (refs₀).Room w vecAt)
    (input : (A.chipBank v floor).Fits w vecAt) (span : (bn₀).rows≤(A.chipBank v floor).size)
    (read : Reads (A.chipBank v floor) chip (bn₀).lanes m)
    (home : (bn₀).hosts=(vx₀).hosts) (lane : (bn₀).lanes=W₀)
    (group : (bn₀).groups=(vx₀).groups*(vx₀).radix)
    (word : (bn₀).bits=(rc₀).size+2)
    (wide : v.vector.bookBits=((rc₀).size+2)*(rc₀).nodes)
    (pages : ∀p q,Measured ((refs₀) p q) (oldBooks p q) (rc₀).nodes W₀ vecAt m)
    (panelLow : A.venue.panel.base+A.venue.panel.size≤ mouthEnd₀)
    (panelSize : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (panelWord : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (earlier : PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree (v.donorEnd floor)≤ps₀)
    (space : headerEnd<2^w) :
    let mouthRows:=v.headerMouthRows floor A mat oldBooks home group word
    let first:=((refs₀).phase w vecAt).image m
    let here:=(v.originAndMouth floor w A mat v.operandShortBits ((refs₀) pg)).image first
    let last:=(v.operandEarlyPhase floor w A).image here
    (∀j f,Held g₀ headerEnd last (v.originAt floor v.operandShortBits shape j f) (v.originHeaderValue shape (oldBooks pg) j f)) ∧
    (∀j f,Held g₀ headerEnd last (v.oldHeaderAt floor j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (v.previousHeaderValue shape oldBooks j f h k))) ∧
    ∀j f,Held g₀ headerEnd last (v.mouthAt floor A mat shape j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (v.mouthHeaderValue floor A mat shape mouthRows chip home group j f h k)) :=by
  let mouthRows:=v.headerMouthRows floor A mat oldBooks home group word
  have mouthMeasured (a l) : Measured (v.mouthRef A mat a l) (mouthRows a l) (rc₀).nodes W₀ vecAt m:=by
    let wanted:=v.headerMouthPage floor A mat a
    exact HeaderWords.reindex_measured mat.newCap.symm home.symm group.symm word.symm ((refs₀) wanted l)
      (oldBooks wanted l) m (pages wanted l)
  exact v.original_headers floor A mat shape refs₀ ((refs₀) pg) (oldBooks pg) mouthRows chip oldBooks m good
    (pages pg) mouthMeasured input span read home lane group wide pages panelLow panelSize panelWord earlier space

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
