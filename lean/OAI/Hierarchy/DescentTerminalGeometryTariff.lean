import OAI.Hierarchy.DescentTerminalBookNative
import OAI.Hierarchy.DescentTerminalCableWidthTape
import OAI.Hierarchy.DescentTerminalPointerPrice
import OAI.Hierarchy.DescentTerminalPrimitiveSpace

namespace OAI
/-! # Charging the earlier six geometry lookups and the private width counter -/
namespace Hierarchy.DescentTerminalGeometryTariff
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalPointerFrame DescentStaticWordColumn
open DescentTerminalGrainProfiles DescentTerminalLocalPortBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section

private theorem sweep {L : ℕ} (src:Fin L→Expr) (w start H i n:ℕ) (room:i+n≤L) (work:∀j,(src j).work≤64) :
    names (ProtocolRAM.program w (DescentPackedFlowBatch.passes start H H (Gather.expression src) i n))≤
      15+267*n := by
  induction n generalizing i with
  | zero=>rw [DescentPackedFlowBatch.passes,ProtocolRAM.program,names_scan];decide
  | succ n ih=>
    rw [DescentPackedFlowBatch.passes,ProtocolRAM.program,names_seq,Pass.procedure,names_scan]
    have e:(Gather.expression src i).work≤64:=by
      rw [Gather.expression,dite_eq_left (by omega : i<L)]
      apply work
    have rest:=ih (i+1) (by omega)
    dsimp only at ⊢
    omega

theorem gathered {L d b:ℕ} (src:Fin L→Expr) (f:(Fin L→Cell d)→Cell b) (w start H:ℕ)
    (work:∀j,(src j).work≤64) :
    let reads:=Gather.reads start H src
    let one:=DescentTerminalPointerFrame.program w (Gather.rom start L H) (Gather.banks (L:=L) start H) H f
    let ticks:=clock reads+((4+10*size L d)+(4+H*(16+26*L)))
    names ((ProtocolRAM.program w reads).seq one)+ticks≤
      1000*(size L d+(H+1)*(L+1)) := by
  dsimp only
  have printable:names (ProtocolRAM.program w (Gather.reads start H src))≤15+267*L:=
    sweep src w start H 0 L (by omega) work
  have duration:=Gather.fetch_price src 64 start H work
  rw [names_seq,shared_hardware]
  nlinarith [Nat.zero_le (H*L),Nat.zero_le (size L d),Nat.zero_le H,Nat.zero_le L]

theorem book {L G V A:ℕ} (C:Print.Layout L) (decode:(Fin L→Cell C.bits)→Directory G V A) (M w:ℕ)
    (work:∀j,(C.source j).work≤64) (n:ℕ) (hn:n≤6) :
    names (C.prefix decode M w n hn)+C.time n hn≤
      19+n*(1000*(size L C.bits+(C.homes+1)*(L+1))) := by
  induction n with
  | zero=>rw [Print.Layout.prefix,Print.Layout.time,ProtocolRAM.program,names_scan,Nat.zero_mul];decide
  | succ n ih=>
    let j:Fin 6:=⟨n,by omega⟩
    have one:=gathered C.source (C.field decode M j) w (C.origin n) C.homes work
    change names (C.one decode M w j)+(_+(_+_))≤_ at one
    have rest:=ih (by omega)
    have step : names (C.one decode M w j) + C.oneTime j ≤
        1000*(size L C.bits+(C.homes+1)*(L+1)) := by
      simpa only [Print.Layout.oneTime, Print.Layout.passes, Nat.add_assoc] using one
    rw [Print.Layout.prefix, Print.Layout.time, names_seq, Nat.succ_mul]
    dsimp only [j] at step
    omega

theorem cable_work {B c G M:ℕ} (T:Counter.Rack B c G M) (j:Fin T.cols) : (T.readCols j).work≤64 := by
  unfold Counter.Rack.readCols Counter.source
  cases (Counter.number B c G M).symm j <;>
    norm_num [Counter.Sockets.ticket, Counter.Sockets.first, Expr.work]

theorem cable {B c G M:ℕ} (T:Counter.Rack B c G M) (w q p:ℕ) :
    names (T.program w q p)+T.time q p ≤
      4000*(T.fee+T.printer.entries+(T.tickets+1)*(T.cols+1)+T.maxRows) := by
  have core:=gathered T.readCols T.gates w T.base T.tickets (cable_work T)
  change names (T.middle w)+T.middleTime≤1000*(T.fee+(T.tickets+1)*(T.cols+1)) at core
  have span:(T.sockets.home T.homes T.degree).size≤2*T.tickets+1:=
    DescentTerminalPrimitiveArena.pad_le T.tickets
  have nm:=T.printer.names_exact q p w
  have ticks:=T.printer.clocks_exact q p
  change T.printer.clocks q p=23+10*T.printer.entries+148*T.tickets+T.maxRows*(if T.tickets=0 then 16 else 26) at ticks
  change names (T.printer.program q p w)=15*(T.printer.entries+1)+(if T.tickets=0 then 340 else 360) at nm
  simp only [Counter.Rack.program,Counter.Rack.time,names_seq,Counter.Sockets.prepare,names_mount]
  split_ifs at ticks nm <;> nlinarith [Nat.zero_le (T.tickets*T.cols),Nat.zero_le T.fee,Nat.zero_le T.maxRows]

/-- The number of input columns, hence the per-host coefficient, contains
only true panels. All pre-remix groups arrive as a single packed digit array. -/
theorem entire_groups (blocks cap groups:ℕ) (nonempty:0<groups) :
    Counter.columns blocks cap groups groups=1+blocks*(2*cap) := by
  have small:chunks groups groups=1:=by
    change (groups+groups-1)/groups=1
    have upper: (groups+groups-1)/groups<2:=(Nat.div_lt_iff_lt_mul nonempty).2 (by omega)
    have lower:1≤(groups+groups-1)/groups:=(Nat.le_div_iff_mul_le nonempty).2 (by omega)
    omega
  simp [Counter.columns,small]

theorem paid {L G V A B c gp mp:ℕ} (C:Print.Layout L) (decode:(Fin L→Cell C.bits)→Directory G V A)
    (M w:ℕ) (T:Counter.Rack B c gp mp) (q p height bw H factor rows:ℕ)
    (fetch:∀j,(C.source j).work≤64)
    (books:size L C.bits≤2^(height/2)) (cables:T.fee≤2^(height/2)) (ceil:T.printer.entries≤4*2^(height/2))
    (bookColumns:(C.homes+1)*(L+1)≤H*factor) (cableColumns:(T.tickets+1)*(T.cols+1)≤H*factor)
    (charged:T.maxRows≤rows) :
    (names (C.prefix decode M w 6 le_rfl)+C.time 6 le_rfl+
      names (T.program w q p)+T.time q p)*(bw+1)≤
      30000*((2^(height/2)+H*factor)*(bw+1)+rows*(bw+1)) := by
  have first:=book C decode M w fetch 6 le_rfl
  have second:=cable T w q p
  have pos:=Nat.two_pow_pos (height/2)
  have raw:names (C.prefix decode M w 6 le_rfl)+C.time 6 le_rfl+names (T.program w q p)+T.time q p≤
      30000*(2^(height/2)+H*factor+rows):=by omega
  calc
    _ ≤(30000*(2^(height/2)+H*factor+rows))*(bw+1):=Nat.mul_le_mul_right _ raw
    _ = _ := by ring

end
end Hierarchy.DescentTerminalGeometryTariff

end OAI
