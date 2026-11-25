import OAI.Hierarchy.DescentDatedOperandHeader
import OAI.Hierarchy.DescentDatedOrdinaryBirthArea
import OAI.Hierarchy.DescentPackedMatchInstalled
import OAI.Hierarchy.DescentPackedCensusIngress
import OAI.Hierarchy.DescentOrdinaryImageIssue
import OAI.Hierarchy.DescentExteriorRotationWord

namespace OAI
/-! # The public machine for one ordinary date -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

open DescentSIMDLookup DescentPackedColony DescentSixParty DescentCompiler ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

namespace Ordinary
variable {F : Type} [Field F] (a : Ordinary) (gadget : PoweredGadget F) (hk : 0 < a.k)
    (i : Operands) (v : Measures) (w floor : ℕ)

local notation "M" => a.lanesAt
local notation "r" => 2^a.k
local notation "K" => 2^(a.k+1)
local notation "p" => 2*a.cap
local notation "c" => a.chooser i.roster floor
local notation "base" => a.sorterAt i.roster floor
local notation "rom" => a.prepareAt i.roster floor
local notation "matchBase" => a.matcherAt i.roster floor
local notation "plan" => a.matcher i.roster floor
local notation "ports" => i.ports a.D
local notation "cables" => fun (x : Fin r) (j : Fin p)=>i.wire x.val j.val
local notation "atom" => fun (x : Fin r)=>i.atoms x.val
local notation "newPorts" => {ports with roster:=Prepare.rosterBank base a.H a.D}
local notation "wins" => (c).winners a.D a.k a.b a.H a.G M
local notation "rule" => Prepare.ROM.chart rom a.D (a.k+3) M a.bits i.actors wins cables
local notation "sort_" => Prepare.ROM.roster rom a.k a.D a.cap (a.k+3) M a.H a.G
  (Prepare.ROM.headBits a.H a.D) i.roster
local notation "steps" => Prepare.passes rule sort_ base a.H a.G M a.D
local notation "gates" => Prepare.gatedBank (k:=a.k) base a.H a.G M a.D a.bits
local notation "marked" => Prepare.markedBank (k:=a.k) (cap:=a.cap) base a.H a.G M a.D a.bits
local notation "fields_" => Gather.expr gates marked newPorts a.H
local notation "q" => Census.order r a.cap
local notation "widths" => fun j=>Census.width a.D a.cap a.b ((q).symm j)
local notation "table" => fun j=>Census.contribution a.D a.cap a.b ((q).symm j)
local notation "read_" => fun j=>Census.expr (Census.Broadcast.result i.hubs floor a.H a.G M) atom
  (fun x t=>Expr.lookup ((cables) x t) .row) ((q).symm j)
local notation "inputWidth" => (1+a.b+2*p)*r
local notation "begin_" => Census.beginSum floor a.H a.G M

def censusImage := Phase.CensusTables.image (w:=w) (c).origin inputWidth (a.b*r) M a.H a.G
  (fun fl=>PackedCensus.lookup fl a.b p a.k v.wire 256 (v.z*gadget.b) v.hist)
def chooserImage := Phase.Arena.image (w:=w) (c).chart hk a.D a.H a.G a.b a.phaseWidth
  (DescentHostDegree.gap a.D) (2^DescentHostDegree.packExponent 20 a.D*((v.wire*(v.z*gadget.b))*a.cap))

def intake : Procedure w :=
  (DescentStaticWordColumn.program w floor (Census.Broadcast.literal a.H a.G M) (2*a.rows)).seq
    (DescentPackedColumnSum.program w begin_ (c).source.base a.unit M inputWidth a.H a.G widths table read_)

def matchCPU : Procedure w :=
  ((Prepare.ROM.program w rom a.k a.D a.cap (a.k+3) a.panelBits M a.H a.G).seq
    (ProtocolRAM.program w steps)).seq
    (Gather.ROM.machine a.shapeAt a.panelBits r a.D p a.cap K a.H a.G M a.unit matchBase a.seats w fields_)

def reportCPU : Procedure w :=
  LayoutSum.Finish.program a.shapeAt M (plan).layout.topology (plan).layout.out a.batch gadget w

def rotationCPU : Procedure w :=
  let start:=a.flagEnd i.roster floor
  let mu:=((c).shelves a.D a.k a.b M).mu
  (DescentExteriorRotationWord.sheet (w:=w) hk start).program.seq
    (scan w (start+2^a.k) 1 (DescentExteriorRotationWord.ordinary mu ⟨start,a.k⟩))

def selected : Procedure w :=
  let prints := (a.censusImage gadget i v w floor).program.seq (a.chooserImage gadget hk i v w floor).program
  let choose := (c).program a.D a.k a.b p a.H a.G M w
  prints.seq ((a.intake i w floor).seq (choose.seq (a.matchCPU i w floor)))

def program : Procedure w :=
  let prints := (a.censusImage gadget i v w floor).program.seq (a.chooserImage gadget hk i v w floor).program
  let choose := (c).program a.D a.k a.b p a.H a.G M w
  (((prints.seq ((a.intake i w floor).seq (choose.seq (a.matchCPU i w floor)))).seq
    (a.reportCPU gadget i w floor)).seq (a.rotationCPU hk i w floor))
def selectedTicks :=
  let prints := 8+10*((a.censusImage gadget i v w floor).length+(a.chooserImage gadget hk i v w floor).length)
  let input := (4+10*(2*a.rows))+DescentPackedColumnSum.ticks begin_ a.unit M a.H a.G widths read_
  let choose := (c).ticks a.D a.k a.b p a.H a.G M w
  let matchingTicks := ((4+10*Prepare.staticWords a.k a.D a.cap (a.k+3) M a.H a.G)+ProtocolRAM.clock steps)+
    Gather.ROM.ticks a.shapeAt a.panelBits r a.D p K a.H a.G M a.unit matchBase a.seats fields_
  prints+(input+(choose+matchingTicks))

def ticks :=
  let prints := 8+10*((a.censusImage gadget i v w floor).length+(a.chooserImage gadget hk i v w floor).length)
  let input := (4+10*(2*a.rows))+DescentPackedColumnSum.ticks begin_ a.unit M a.H a.G widths read_
  let choose := (c).ticks a.D a.k a.b p a.H a.G M w
  let matchingTicks := ((4+10*Prepare.staticWords a.k a.D a.cap (a.k+3) M a.H a.G)+ProtocolRAM.clock steps)+
    Gather.ROM.ticks a.shapeAt a.panelBits r a.D p K a.H a.G M a.unit matchBase a.seats fields_
  (((prints+(input+(choose+matchingTicks)))+LayoutSum.Finish.ticks a.shapeAt M a.batch)+((4+10*(2^a.k-1))+30))
theorem same_program {b : Ordinary} (hb : 0 < b.k) (data : Measures) (size : a=b) (values : v=data) :
    a.program gadget hk i v w floor=b.program gadget hb i data w floor ∧
      a.ticks gadget hk i v w floor=b.ticks gadget hb i data w floor := by
  subst b
  subst data
  exact ⟨rfl,rfl⟩

end Ordinary
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
