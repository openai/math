import OAI.Hierarchy.DescentPackedMatchPrepared
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # Exact halt time of the ordinary matcher on arbitrary memory contents -/
namespace Hierarchy.DescentPacking.PackedMatch
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section
variable {w k D cap H G M R n short : ℕ}

namespace ProfileTable
theorem any (s : Shape) (l : ProfileTable.Layout) (r : ProfileTable.Room s M R n w l) (m : Memory w) :
    (ProfileTable.issue w R n l).Exec m (ProfileTable.issued l R n m) (ProfileTable.clock n) := by
  let pre:=ProfileTable.boot l n m
  let mid:=ProfileTable.middle l R n m
  have lo:=r.low
  have size:=r.size
  have past:=r.cursor.2.2
  have end_:=r.scan.space
  have extent : l.counts+n<2^w := by omega
  have cap_ : PackedProfileCursor.addr l.cursor.base n+2<2^w := by unfold PackedProfileCursor.addr;omega
  have first : (scan w l.counts n (sumLookup l.countROM l.topology)).Exec m pre (4+28*n) := by
    have safe : (sumLookup l.countROM l.topology).Fits w l.counts := ⟨r.counter,r.topology,trivial⟩
    rw [Nat.mul_comm 28 n]
    intro pcs regs pubs cpu
    exact scan_exec l.counts n (sumLookup l.countROM l.topology) m safe extent cpu
  have second : (PackedProfileCursor.program w R l.counts l.cursor.base n).Exec pre mid (PackedProfileCursor.ticks n) :=
    PackedProfileCursor.run R l.counts l.cursor.base n pre r.low cap_
  let e:=programExpr l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor)
  have last : (scan w l.out n e).Exec mid (issued l R n m) (4+152*n) := by
    rw [Nat.mul_comm 152 n]
    exact (ProfileTable.exec s l.tables l.topology l.raw (pointer l.cursor) (rem_ l.cursor) r.scan mid).1
  intro pcs regs pubs cpu
  exact Procedure.Exec.then (Procedure.Exec.then first second) last cpu

end ProfileTable

namespace Local.Gather.ROM
set_option maxHeartbeats 2400000 in
theorem any (s : Shape) (r p K B unit base seats : ℕ) (field : Fin (Local.fields r D p)→Expr)
    (m : Memory w) (large : Local.Gather.matchUnit s short r D p≤unit) (shifts : unit*M≤w/2)
    (space : (place s short r D p K H G M unit base seats).endAddr<2^w) (below : ∀i,(field i).Fits w base) :
    (machine s short r D p B K H G M unit base seats w field).Exec m
      (after s short r D p B K H G M unit base seats field m)
      (ticks s short r D p K H G M unit base seats field) := by
  let P:=place s short r D p K H G M unit base seats
  let c:=chart s short r D p K H G M (M*s.pairs) unit base P.source
  let input:=mounted s short r D p B K H G M (M*s.pairs) unit base m
  let rows:=H*chunks G M
  let n':=(K*H)*chunks G M
  let ps:=Local.Gather.passes c.joins field c.desc c.mask P.source.base H G M
  let mid:=ProtocolRAM.result ps input
  let topo:=PackedMatch.result c.lookup P.layout.topology.base (K*H) G M mid
  have A:=arranged s short r D p K H G M unit base seats w large shifts space
  have initial : Procedure.Exec _ _ _ _ := run s short r D p B K H G M (M*s.pairs) unit base m A.romEnd
  let es:=Local.Gather.allExprs c.joins field c.desc c.mask
  have safe (e : Expr) (he : e∈es) : e.Fits w P.source.base := by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    simp [Local.Gather.lookup,Expr.Fits,Local.Gather.assembly,
      Local.Gather.fits c.joins field P.source.base (A.gather field below)]
    exact ⟨A.descriptors j,A.mask.1⟩
  have bound : P.source.base+es.length*rows<2^w := by
    have span:=A.fit.srcSize
    change n'≤P.source.size at span
    have total : K*rows≤P.source.size := by simpa only [n',rows,Nat.mul_assoc] using span
    rw [show es.length=K from List.length_ofFn]
    exact (Nat.add_le_add_left total _).trans_lt (A.fit.source.2.2.trans_lt ((Nat.le_add_right ..).trans_lt A.fit.output))
  have blocks : (ProtocolRAM.program w ps).Exec input mid (ProtocolRAM.clock ps) :=
    ProbeStage.Native.columns_exec es input (ProbeStage.Native.columns_safe es le_rfl safe bound)
  have ok : (DescentSIMDLookup.lookup c.lookup).Fits w P.layout.topology.base :=
    ⟨⟨A.fit.dictionary,A.fit.source,trivial⟩,A.fit.mask,trivial⟩
  have topoRun : (physical c.lookup P.layout.topology.base (K*H) G M w).Exec mid topo (4+44*n') := by
    rw [show 4+44*n' = 4+n'*(2*(DescentSIMDLookup.lookup c.lookup).work+4) by
      rw [lookup_work,Nat.mul_comm 44]]
    exact scan_exec P.layout.topology.base n' (DescentSIMDLookup.lookup c.lookup) mid ok A.fit.output
  have profiles : Procedure.Exec _ _ _ _ := ProfileTable.any s P.layout A.room topo
  intro npc nreg nslot mach
  exact Procedure.Exec.then @initial (Procedure.Exec.then @blocks (Procedure.Exec.then @topoRun @profiles)) mach

end Local.Gather.ROM

end
end Hierarchy.DescentPacking.PackedMatch

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section
variable {k D cap a short H G M w : ℕ}
variable (s : Shape) (K B unit romBase seats : ℕ) (P : Ports D)
    (act : Bank) (vals : Fin (2^k)→Bank) (wire : Fin (2^k)→Fin (2*cap)→Bank)
set_option quotPrecheck false
local notation "base" => Prepare.ROM.sortBase romBase k D cap a M H G
local notation "rbits" => Prepare.bits H G M
local notation "C" => Prepare.ROM.chart romBase D a M rbits act vals wire
local notation "Z" => Prepare.ROM.roster romBase k D cap a M H G (Prepare.ROM.headBits H D) P.roster
local notation "ps" => Prepare.passes C Z base H G M D
local notation "afterPrep" => Prepare.next k H G M D cap base
local notation "field" => Gather.expr (Prepare.gatedBank (k:=k) base H G M D rbits)
  (Prepare.markedBank (k:=k) (cap:=cap) base H G M D rbits) {P with roster:=Prepare.rosterBank base H D} H
local notation "placed" => Gather.ROM.place s short (2^k) D (2*cap) K H G M unit afterPrep seats
local notation "warm" => Prepare.ROM.program w romBase k D cap a short M H G
local notation "matchCPU" => Gather.ROM.machine s short (2^k) D (2*cap) B K H G M unit afterPrep seats w field

set_option maxHeartbeats 1500000 in
/-- Every contents of the input and selector arrays takes the same steps. Each
variable address in the field and profile scans is a bounded bank lookup. -/
theorem any (input : Prepare.ROM.OldRoom act vals wire P.roster H G D M w romBase)
    (ports : Accessible P act H G M w romBase) (key : M*max (DescentSignedCableCodec.width D cap) short≤w/2)
    (large : Gather.matchUnit s short (2^k) D (2*cap)≤unit) (bits : unit*M≤w/2)
    (range : max H D<2^w) (space : (placed).endAddr<2^w) (m : Memory w) :
    let setup:=Prepare.ROM.after romBase k D cap a short M H G m
    let reached:=ProtocolRAM.result ps setup
    (((warm).seq (ProtocolRAM.program w ps)).seq matchCPU).Exec m
      (Gather.ROM.after s short (2^k) D (2*cap) B K H G M unit afterPrep seats field reached)
      (((4+10*Prepare.staticWords k D cap a M H G)+clock ps)+Gather.ROM.ticks s short (2^k) D (2*cap) K H G M unit afterPrep seats field) := by
  intro setup reached
  have start : afterPrep≤(placed).raw.base := ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have last : (placed).raw.base≤(placed).endAddr := by
    iterate 6 apply Nat.le_trans _ (Nat.le_add_right ..)
    exact le_rfl
  have room : afterPrep<2^w:=start.trans_lt (last.trans_lt space)
  have earlier : Prepare.stop k H G M D cap base≤afterPrep := (Nat.le_add_right ..).trans (le_max_left ..)
  obtain ⟨sep,ready,sort_⟩:=Prepare.ROM.arranged romBase k D cap a short M H G w act vals wire P.roster
    input key range (earlier.trans_lt room)
  have before : base≤afterPrep:=(Nat.le_add_right base (Prepare.rosterBank base H D).size).trans (le_max_right ..)
  have old:=Chooser.accessible_before P act ports ((Nat.le_add_right ..).trans sep)
  obtain ⟨access,marked,_,_⟩:=Prepare.space (k:=k) (cap:=cap) P base act old room
  have first : (warm).Exec m setup (4+10*Prepare.staticWords k D cap a M H G) :=Prepare.ROM.run romBase k D cap a short M H G m (sep.trans_lt (before.trans_lt room))
  have execute : (ProtocolRAM.program w ps).Exec setup reached (clock ps) :=Prepare.exec C Z base setup ready sort_
  have read:=early_expr (Prepare.gatedBank (k:=k) base H G M D rbits) (Prepare.markedBank (k:=k) (cap:=cap) base H G M D rbits)
    {P with roster:=Prepare.rosterBank base H D} afterPrep access marked
  intro cpus regs ports machine
  exact Procedure.Exec.then (Procedure.Exec.then first execute)
    (Gather.ROM.any s (2^k) (2*cap) K B unit afterPrep seats field reached large bits space read) machine

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
