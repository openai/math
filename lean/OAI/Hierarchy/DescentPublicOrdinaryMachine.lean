import OAI.Hierarchy.DescentRegisteredOrdinaryBody
import OAI.Hierarchy.DescentNamedRegisteredPrograms
import OAI.Hierarchy.DescentRegisteredOrdinaryStep

namespace OAI
/-! # The ordinary machine selected by the calendar and the previous register bank -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPackedProfileInstall
open DescentPackedProfileArchive DescentTerminalEpochChart DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

namespace DatePorts
variable {F : Type} [Field F] (prior : DatePorts) (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule)
    (op : RotorSpec) (gain k i p tail f drift degree payload seats root : ℕ) (ordinary : ℕ→Dated.Ordinary)
local notation "regs" => VenueProgram.Registered.atAge G S op gain k i p tail f drift degree payload seats root prior ordinary
local notation "stage" => PhysicalOrdinary.StaticCore.profileStart G S gain k i p payload seats root
local notation "data₀" => PhysicalOrdinary.bareData G S i payload seats stage (S.censusBits p) prior (regs).core (regs).installed (regs).clip

/-- Every item in this condition is a numerical dimension equality or a positive size. -/
def MachineFits : Prop :=∃ v:(data₀).Valid,(regs).BodyFits ((data₀).plan v)

local notation "fit" => MachineFits prior G S op gain k i p tail f drift degree payload seats root ordinary
variable (w shelf header : ℕ) (pos : 0<k)

/-- The physical dictionary installed from the original ballot shelf before the match. -/
def profileCode (a : Dated.Ordinary) (old : Bank) (pitch : ProfileRepack) (root shelf w : ℕ) : PrintedStep w :=
  let src:=sourceBank shelf pitch.seats pitch.oldLanes
  let dst:=(a.matcher old (pitch.endAddress root)).raw
  ⟨DescentPackedProfileRepack.program root pitch.seats pitch.oldLanes pitch.newLanes pitch.bits a.shapeAt.digit src dst w,
   DescentPackedProfileRepack.ticks root pitch.seats pitch.oldLanes pitch.newLanes pitch.bits src dst⟩

def commonOrdinary (h : fit) : DateCode w :=
  let b:=(regs).body G ((data₀).plan (Classical.choose h)) stage prior w (Classical.choose_spec h)
  let a:=(regs).core.area
  let pitch:ProfileRepack:=⟨seats,DescentPackedEpochShelves.grain (payload/2) G.C,a.lanesAt*a.shapeAt.pairs,
    DescentTerminalEpochBits.width G.C⟩
  let load:=profileCode a prior.io.roster pitch root shelf w
  (DonorDate.atDate G S gain k i p).codeLoadedAfter G pos payload seats (S.censusBits p) stage header w prior.io
    (regs).core.measures load.program load.ticks b.printed.program b.printed.ticks

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
