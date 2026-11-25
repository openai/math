import OAI.Hierarchy.DescentPackedOrdinaryRotation
import OAI.Hierarchy.DescentDatedOrdinaryProgram
import OAI.Hierarchy.DescentExteriorRotationWord

namespace OAI
/-! # The exact native program on every concrete old world agrees with its public date code -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (hosts : V≃Fin L) (hv : L ≤ 2^ℓ)
    (b payload unit ratio profile seats : ℕ) (input : Dated.Operands) (floor : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "date" => (⟨H,G,k,b,A.degree,A.cap,payload,unit,profile,seats⟩ : Dated.Ordinary)
local notation "measure" => (⟨A.wire,A.z,A.hist⟩ : Dated.Measures)
local notation "C" => (date).chooser input.roster floor
local notation "romBase" => (date).prepareAt input.roster floor
local notation "rdx" => 2^k
local notation "cap2" => 2*A.cap
local notation "K" => 2^(k+1)
local notation "panelBits" => max (k+3) (Nat.clog 2 (A.degree+1))
local notation "s" => shape rdx A.degree cap2 profile
local notation "grain" => M*(s).pairs
local notation "P₀" => input.ports A.degree
local notation "act" => input.actors
local notation "wire" => fun (x : Fin rdx) (j : Fin cap2)=>input.wire x.val j.val
local notation "vals" => (C).winners A.degree k b H G M
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap (k+3) M H G
local notation "bits_" => Prepare.bits H G M
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "prep" => Prepare.ROM.chart romBase A.degree (k+3) M bits_ act vals wire
local notation "sort_" => Prepare.ROM.roster romBase k A.degree A.cap (k+3) M H G (Prepare.ROM.headBits H A.degree) (P₀).roster
local notation "ps" => Prepare.passes prep sort_ base H G M A.degree
local notation "wins_" => Prepare.gatedBank (k:=k) base H G M A.degree bits_
local notation "marks_" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree bits_
local notation "field" => Gather.expr wins_ marks_ {P₀ with roster:=outB} H
local notation "plan" => Gather.ROM.place s panelBits rdx A.degree cap2 K H G M unit nextBase seats
local notation "stamp" => Prepare.ROM.program w romBase k A.degree A.cap (k+3) panelBits M H G
local notation "matcher" => Gather.ROM.machine s panelBits rdx A.degree cap2 A.cap K H G M unit nextBase seats w field
local notation "warm" => (stamp).seq (ProtocolRAM.program w ps)
local notation "before" => (C).program A.degree k b cap2 H G M w
local notation "time₀" => (C).ticks A.degree k b cap2 H G M w
local notation "time₁" => ((4+10*Prepare.staticWords k A.degree A.cap (k+3) M H G)+ProtocolRAM.clock ps)+
  Gather.ROM.ticks s panelBits rdx A.degree cap2 K H G M unit nextBase seats field

local notation "origin" => floor
local notation "hubBank" => input.hubs
local notation "atom" => fun (x : Fin rdx)=>input.atoms x.val
local notation "liveRows" => H*chunks G M
local notation "col" => Census.order rdx A.cap
local notation "startSum" => Census.beginSum origin H G M
local notation "oldBits" => fun i=>(Census.width A.degree A.cap b ((col).symm i))
local notation "func" => fun i=>(Census.contribution A.degree A.cap b ((col).symm i))
local notation "src" => fun i=>(Census.expr (Census.Broadcast.result hubBank origin H G M) atom
  (fun x j=>Expr.lookup ((wire) x j) .row) ((col).symm i))
local notation "outBits" => (1+b+2*cap2)*rdx
local notation "header" => DescentStaticWordColumn.program w origin (Census.Broadcast.literal H G M) (2*liveRows)
local notation "sumCPU" => DescentPackedColumnSum.program w startSum (C).source.base unit M outBits H G oldBits func src
local notation "initCPU" => (header).seq sumCPU
local notation "timeInit" => (4+10*(2*liveRows))+DescentPackedColumnSum.ticks startSum unit M H G oldBits src

local notation "CI" => Phase.CensusTables.image (w:=w) (C).origin ((1+b+2*cap2)*rdx) (b*rdx) M H G
  (fun fl=>PackedCensus.lookup fl b cap2 k A.wire 256 (A.z*gadget.b) A.hist)
local notation "PI" => Phase.Arena.image (w:=w) (C).chart A.fieldBits A.degree H G b
  (2*Phase.unit k b*M) (DescentHostDegree.gap A.degree)
  (2^DescentHostDegree.packExponent 20 A.degree*((A.wire*(A.z*gadget.b))*A.cap))
local notation "publish" => (CI).program.seq (PI).program

local notation "N" => (K*H)*chunks G M
local notation "top" => (plan).layout.topology
local notation "profiles" => (plan).layout.out
local notation "ft" => LayoutSum.Finish.first top profiles N
local notation "B" => LayoutSum.Finish.chart s M top profiles N
local notation "births" => LayoutSum.Finish.births s M top profiles N
local notation "doneAt" => LayoutSum.Finish.stop s M top profiles N
local notation "suffix" => LayoutSum.Finish.program s M top profiles N gadget w
local notation "tock" => LayoutSum.Finish.ticks s M N
local notation "sh" => (C).shelves A.degree k b M
local notation "sheet" => DescentExteriorRotationWord.sheet (w:=w) A.fieldBits doneAt
local notation "rotOut" => doneAt+2^k
local notation "rotEnd" => rotOut+1
local notation "expr" => DescentExteriorRotationWord.ordinary (sh).mu ⟨doneAt,k⟩
local notation "writeRot" => (sheet).program.seq (scan w rotOut 1 expr)
local notation "rotTime" => (4+10*(2^k-1))+30

local notation "full" => ((((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).seq suffix).seq writeRot)
local notation "clock_" => (((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock)+rotTime

/-- The program and clock in the semantic ordinary-stage theorem both reduce to
the instruction sequence obtained from the public integer layout. -/
theorem physical_program :
    full=(date).program gadget A.fieldBits input measure w floor ∧
      clock_=(date).ticks gadget A.fieldBits input measure w floor := ⟨rfl,rfl⟩

theorem physical_any (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (setup : Chooser.Geometry (G:=G) (w:=w) A hosts hv C b cap2 payload unit ratio rs)
    (prior : Accessible P₀ act H G M w floor)
    (oldPort : ∀x j,((wire) x j).Fits w floor ∧ liveRows ≤ ((wire) x j).size)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap)) ≤ unit)
    (flagFits : (hubBank).Fits w floor) (atomFit : ∀x,((atom) x).Fits w floor)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M ≤ (C).source.base)
    (low : (C).chart.weights.base ≤ romBase)
    (next : (C).last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1)) ≤ romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2 ≤ unit)
    (ceilingC : (CI).low+(CI).length ≤ (plan).raw.base) (ceilingP : (PI).low+(PI).length ≤ (plan).raw.base)
    (birthUnit : SixBirths.unit s ≤ unit) (endRoom : rotEnd < 2^w) (m : Memory w) :
    ∃out,((date).program gadget A.fieldBits input measure w floor).Exec m out
      ((date).ticks gadget A.fieldBits input measure w floor) := by
  exact cpu_installed_rotation_any A hosts hv C b payload unit ratio profile seats romBase P₀ act wire floor
    hubBank atom rs setup floor (le_refl _) prior oldPort inputs flagFits atomFit allocated low next large
    ceilingC ceilingP birthUnit endRoom m

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
