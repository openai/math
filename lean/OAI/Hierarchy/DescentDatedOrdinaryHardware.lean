import OAI.Hierarchy.DescentDatedOrdinaryProgram
import OAI.Hierarchy.DescentPackedOrdinaryPublicHardware

namespace OAI
/-! # Control storage of the same date-only ordinary instruction tape -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSIMDLookup DescentPackedColony DescentSixParty DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F : Type} [Field F] (a : Ordinary) (gadget : PoweredGadget F) (hk : 0 < a.k)
  (i : Operands) (v : Measures) (w floor : ℕ)

set_option quotPrecheck false
local notation "M" => a.lanesAt
local notation "q" => a.chooser i.roster floor
local notation "base" => a.sorterAt i.roster floor
local notation "rom" => a.prepareAt i.roster floor
local notation "mb" => a.matcherAt i.roster floor
local notation "nextPorts" => {(i.ports a.D) with roster:=Prepare.rosterBank base a.H a.D}
local notation "bits_" => Prepare.bits a.H a.G M
local notation "wires" => fun (x : Fin (2^a.k)) (j : Fin (2*a.cap))=>i.wire x.val j.val
local notation "gate" => Prepare.gatedBank (k:=a.k) base a.H a.G M a.D bits_
local notation "marked" => Prepare.markedBank (k:=a.k) (cap:=a.cap) base a.H a.G M a.D bits_
local notation "setup" => Prepare.ROM.chart rom a.D (a.k+3) M bits_ i.actors
  ((q).winners a.D a.k a.b a.H a.G M) wires
local notation "sort_" => Prepare.ROM.roster rom a.k a.D a.cap (a.k+3) M a.H a.G (Prepare.ROM.headBits a.H a.D) i.roster
local notation "choose" => (q).program a.D a.k a.b (2*a.cap) a.H a.G M w
local notation "core" => (a.intake i w floor).seq ((choose).seq (a.matchCPU i w floor))
local notation "ci" => a.censusImage gadget i v w floor
local notation "pi" => a.chooserImage gadget hk i v w floor
local notation "N" => Census.columns (2^a.k) a.cap
local notation "K" => 2^(a.k+1)
local notation "s" => a.shapeAt

theorem cheap : CheapCode (a.program gadget hk i v w floor) := by
  unfold program
  dsimp only
  refine @cheap_seq w _ _ ?_ ?_
  · refine @cheap_seq w _ _ ?_ ?_
    · refine @cheap_seq w _ _ (@cheap_seq w _ _ (ci).hardware.1 (pi).hardware.1) ?_
      refine @cheap_seq w (a.intake i w floor) ((choose).seq (a.matchCPU i w floor)) ?_ ?_
      · unfold intake
        exact @cheap_seq w _ _ (@DescentPackedColumnSum.mount_cheap w _ _ _)
          (@DescentPackedColumnSum.program_cheap N w _ _ _ _ _ _ _ _ _ _)
      · exact @ordinary_cheap a.k a.D a.cap s q setup sort_ nextPorts gate marked rom base mb a.seats a.panelBits
          (a.k+3) K a.H a.G M a.unit w a.b (2*a.cap)
    · unfold reportCPU LayoutSum.Finish.program
      refine @cheap_seq w _ _ (@cheap_seq w _ _ (@DescentPackedColumnSum.mount_cheap w _ _ _) (@scan_cheap w _ _ _)) ?_
      exact @LayoutSum.cheap F _ a.batch M w s _ gadget
  · unfold rotationCPU
    exact @cheap_seq w _ _ (@DescentPackedColony.Phase.Arena.Image.hardware w
      (DescentExteriorRotationWord.sheet (w:=w) hk (a.flagEnd i.roster floor))).1 (@scan_cheap w _ _ _)

theorem controls (bound volume : ℕ) (bounded : ∀x : Fin (2^a.k),(i.atoms x.val).work ≤ bound)
    (live : 0 < a.rows) (gates : ((1*2^a.k)+(a.k+3))*M ≤ a.payload/2)
    (cables : DescentSignedCableCodec.width a.D a.cap*M ≤ a.payload/2)
    (pages : a.unit*M ≤ a.payload/2) (fund : 2^(a.payload/2) ≤ volume)
    (hosts : a.H ≤ volume) (rows : a.rows ≤ volume) :
    names (a.program gadget hk i v w floor) ≤
      15*((ci).length+(pi).length+2)+
      ((15*(2*a.rows+1)+15*(N*2^(a.unit*M)+1)+15+4*N*((max 22 bound)+6))+
        (4*(q).ticks a.D a.k a.b (2*a.cap) a.H a.G M w+Prepared.namesPerWord a.k a.D a.cap K*volume))+
      ((126+15*SixBirths.entries s M)+(30*(2^(SixBirths.width s M)+1)+265))+
      (15*((2^a.k-1)+1)+55) := by
  let order:=Census.order (2^a.k) a.cap
  let b (j : Fin N):=Census.width a.D a.cap a.b (order.symm j)
  let f (j : Fin N):=Census.contribution a.D a.cap a.b (order.symm j)
  let read (j : Fin N):=Census.expr (Census.Broadcast.result i.hubs floor a.H a.G M)
    (fun x=>i.atoms x.val) (fun x t=>Expr.lookup (i.wire x.val t.val) .row) (order.symm j)
  have cost:=from_old_hardware s q setup sort_ nextPorts gate marked rom base mb a.seats a.panelBits
    (a.k+3) K a.H a.G M a.unit w a.b (2*a.cap) floor (q).source.base ((1+a.b+2*(2*a.cap))*2^a.k)
    b f read (max 22 bound) (fun j=>Census.source_work a.k a.cap a.H a.G M floor i.hubs
      (fun x=>i.atoms x.val) wires bound bounded (order.symm j)) live a.payload volume gates cables pages fund hosts rows
  have emit:=LayoutSum.Finish.hardware s M (a.matcher i.roster floor).layout.topology
    (a.matcher i.roster floor).layout.out a.batch gadget w
  let sheet:=DescentExteriorRotationWord.sheet (w:=w) hk (a.flagEnd i.roster floor)
  have len : sheet.length=2^a.k-1 := by
    change a.flagEnd i.roster floor+(2^a.k-1)-a.flagEnd i.roster floor=_
    omega
  change names (((((ci).program.seq (pi).program).seq core).seq (a.reportCPU gadget i w floor)).seq
    (a.rotationCPU hk i w floor)) ≤ _
  rw [names_seq,names_seq,names_seq,names_seq,(ci).hardware.2,(pi).hardware.2]
  have rotation : names (a.rotationCPU hk i w floor)=15*((2^a.k-1)+1)+55 := by
    change names (sheet.program.seq _) = _
    rw [names_seq,sheet.hardware.2,len,names_scan]
    rfl
  rw [rotation,show names (a.reportCPU gadget i w floor)=_ from emit]
  have inner : names core ≤ _ := cost.2
  have rowCount : a.rows=a.H*chunks a.G M := rfl
  omega

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
