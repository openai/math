import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentNamedOriginalInputs
import OAI.Hierarchy.DescentResetOriginalDonorSensors
import OAI.Hierarchy.DescentResetOriginalZeroHalo

namespace OAI
/-! # The fixed original-number inputs of the scheduled physical reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (v : ResetOutput)
local notation "s" => v.sheets

def originalAux (base : ℕ) (j : Fin 4) : Bank:=
  DescentResetPeerJointPacked.Aux.bank (DescentResetPeerJointPacked.endAddress (v.massEnd base)
    (s).hosts v.front.peer.hosts (s).groups (s).lanes (s).metaBits) (s).hosts j

def originalWordsBase (base : ℕ):=(s).stemSources.endAddress ((s).metaEnd (v.remap base).endAddress)

def originalDonorBase (base : ℕ):=DescentResetOriginalZeroHalo.endAddress (v.originalWordsBase base)
  (s).hosts (s).groups (s).lanes (s).metaBits

def originalDonorLayout (N : ℕ) : DescentResetOriginalDonors.Layout :=
  ⟨v.front.peer.hosts,(s).groups,(s).blocks,(s).lanes,N,(s).stemSignedBits,(s).metaBits,(s).selectorBits,(s).shortBits⟩

/-- The first public column is the separately measured trunk. The others use
the contact slots already written by the candidate metadata phase. -/
def originalMeta (base x : ℕ) (j : Fin ((s).contacts+1)) : Expr:=
  Fin.cases (v.front.trunkOperand (v.actorEnd base) x) (fun j=>
    .lookup (((s).masks (v.remap base).endAddress).output 9 (s).metaBits (x*((s).contacts+(s).privates)+j.val)) .row) j

def originalPrivate (base x j : ℕ) : Expr:=.lookup (((s).masks (v.remap base).endAddress).output 9 (s).metaBits
    (x*((s).contacts+(s).privates)+(s).contacts+j)) .row

def originalZero (base x : ℕ) : Expr:=DescentResetOriginalZeroHalo.zero (v.originalWordsBase base)
  (s).hosts (s).groups (s).lanes (s).metaBits x

def originalHalo (base : ℕ) : Expr:=DescentResetOriginalZeroHalo.halo (v.originalWordsBase base)
  (s).hosts (s).groups (s).lanes (s).metaBits (v.originalAux base 0)

def originalPrior (base N : ℕ) : DescentResetPublicOriginalPhase.Prior (s).blocks (s).contacts N :=
  let J:=v.originalDonorLayout N
  let p:=v.originalDonorBase base
  let b:=v.originalWordsBase base
  let dir:=v.actor.directory (v.middle.stop base)
  { «meta»:=fun x=>v.originalMeta base x.val
    zero:=fun x=>v.originalZero base x.val
    self:=fun _=>DescentResetOriginalZeroHalo.self b (s).hosts (s).groups (s).lanes (s).metaBits (v.originalAux base 0)
    shape:=fun _=>DescentResetOriginalZeroHalo.shape b (s).hosts (s).groups (s).lanes (s).metaBits (v.originalAux base 1)
    label:=J.label p (v.remap base) dir.count dir.inverse
    cargo:=J.cargo p (v.remap base) dir.count dir.inverse }

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))

set_option maxRecDepth 4096 in
/-- The compiler fixes every clause before the reset chooser runs. The stem
registers are installed by `DateInputs.numbered` on the measured date. -/
def namedNumber (earlier : (v).OriginalOperands base₀) : (v).sheets.OriginalInputs:=
  let sensor:=(v).contactShape.originalSensorsAt ((v).front.donorStart ((v).actorEnd base₀))
    ((v).trunkEnd base₀) (((v).issuedScene base₀ earlier).donor) ((v).sheets.originalDonors.slots)
  CandidateSheets.OriginalInputs.fromBoard S board k tail age venue.degree f g cap M sensor
    ((v).originalPrior base₀ ((2^k)*(2*cap))) (fun _ _ _=>.lit 0)
    (fun x j=>(v).originalPrivate base₀ x.val j.val) (fun x=>(v).originalZero base₀ x.val)
    (fun _=>(v).originalHalo base₀)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
