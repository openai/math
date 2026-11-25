import OAI.Hierarchy.DescentPublicDonorPhase
import OAI.Hierarchy.DescentOrdinaryPhysicalProgram
import OAI.Hierarchy.DescentDatedOrdinaryBirthArea

namespace OAI
/-! # Literal matcher output addresses for every donor operand and the next free word -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentCompiler DescentHostDegree DescentRawCablePanel DescentSIMDLookup
open DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentPackedZip DescentPackedColony DescentHostDirectory ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable (d : DonorDate) (payload seats : ℕ) (input : Dated.Operands)
local notation "r" => 2^d.exponent
local notation "K" => 2^(d.exponent+1)
local notation "H" => d.hosts
local notation "J" => d.groups
local notation "M" => lanes payload d.amount
local notation "s" => d.matcher
local notation "short" => (d.format).short

def matcherOutput (romBase : ℕ) : OrdinaryLink.PriorBanks r d.degree d.cap K :=
  let bump:=Prepare.ROM.sortBase romBase d.exponent d.degree d.cap (d.exponent+3) M H J
  let bits:=Prepare.bits H J M
  let next:=Prepare.next d.exponent H J M d.degree d.cap bump
  let plan:=Gather.ROM.place s short r d.degree (2*d.cap) K H J M d.amount next seats
  let books:=Gather.ROM.chart s short r d.degree (2*d.cap) K H J M (M*(s).pairs) d.amount next plan.source
  let rows:=(K*H)*chunks J M
  let top:=plan.layout.topology
  let profiles:=plan.layout.out
  let finish:=LayoutSum.Finish.chart s M top profiles rows
  let births:=LayoutSum.Finish.births s M top profiles rows
  { gate:=⟨finish.out,0⟩
    hub:=input.hubs
    peers:={input.ports d.degree with roster:=Prepare.rosterBank bump H d.degree}
    winners:=Prepare.gatedBank (k:=d.exponent) bump H J M d.degree bits
    marked:=Prepare.markedBank (k:=d.exponent) (cap:=d.cap) bump H J M d.degree bits
    signed:=fun x bin=>input.wire x.val bin.val
    operands:=books.joins
    topology:=top
    born:=⟨births,Nat.clog 2 rows⟩ }

/-- All turns read the previous matching stage's actual six numerical shelves. -/
def matchedPhase (romBase setupBase bw : ℕ) :=
  d.phase payload setupBase bw (d.matcherOutput payload seats input romBase)

def schedule (board : ℕ) : Dated.Ordinary :=
  ⟨H,J,d.exponent,board,d.degree,d.cap,payload,d.amount,DescentTerminalEpochBits.width d.colors,seats⟩

def afterMatcher (board floor bw : ℕ) :=
  let a:=d.schedule payload seats board
  d.matchedPhase payload seats input (a.prepareAt input.roster floor) (a.rotationEnd input.roster floor) bw

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
