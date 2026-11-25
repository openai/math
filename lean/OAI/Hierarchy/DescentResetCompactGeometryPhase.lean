import OAI.Hierarchy.DescentResetCompactSelf
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # One measured raster for the public compact self-halo and shape -/
namespace Hierarchy.DescentResetCompactGeometry
open DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Chart where
  inverse : Bank
  count : Bank
  ranks : Bank
  base : ℕ
  geometry : ℕ
  self : Bank
  broadcast : ℕ
  hosts : ℕ
  oldHosts : ℕ
  shapes : ℕ
  groups : ℕ
  lanes : ℕ
  bits : ℕ

namespace Chart
variable (C : Chart) {w : ℕ}
def raw:=C.oldHosts*C.shapes
def choose (t : Fin 2):=if t=0 then output C.geometry C.hosts 0 else C.self
def pull:=selfExpr C.count (output C.geometry C.hosts 1) C.ranks
def size:=DescentResetHaloBroadcast.count C.hosts C.groups C.lanes C.bits
def lit:=DescentResetHaloBroadcast.literal C.bits C.groups C.lanes (id : Fin C.hosts→Fin C.hosts)
def top:=DescentResetHaloBroadcast.endAt C.broadcast C.hosts C.groups C.lanes C.bits
def first (m : Memory w):=after C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts m
def second (m : Memory w):=image C.self.base C.hosts C.pull (C.first m)
def finalMem (m : Memory w):=DescentStaticWordColumn.image C.broadcast C.lit (C.second m) C.size
def cpu (w : ℕ):=((phase C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts w).seq
  (scan w C.self.base C.hosts C.pull)).seq (DescentStaticWordColumn.program w C.broadcast C.lit C.size)
def clock:=ticks C.inverse C.count C.base C.raw C.geometry C.hosts+(4+C.hosts*(2*C.pull.work+4))+(4+10*C.size)
def port (t : Fin 2):=DescentResetHaloBroadcast.expr (C.choose t) C.broadcast C.hosts C.groups C.lanes C.bits

structure Room (w : ℕ) : Prop where
  here : C.inverse.Fits w C.base
  cnt : C.count.Fits w C.base
  ranks : C.ranks.Fits w C.base
  header : C.base+words C.raw≤C.geometry
  selfAfter : stop C.geometry C.hosts≤C.self.base
  selfBank : C.self.Fits w C.broadcast
  selfRows : C.hosts≤C.self.size
  broad : C.top<2^w

theorem cut (r : C.Room w) : C.broadcast+C.size<2^w:=by
  have size:=Nat.le_pow_clog (by decide : 1<2) (C.size+1)
  have far:=r.broad
  change C.broadcast+2*(C.hosts*chunks C.groups C.lanes)+2^(Nat.clog 2 (C.size+1))<2^w at far
  omega

theorem shelf (r : C.Room w) (s : Fin 2) : (output C.geometry C.hosts s).Fits w C.self.base:=by
  have fit:=Nat.mul_le_mul_right (DescentResetOriginalSlots.stride C.hosts) s.isLt
  rw [Nat.succ_mul] at fit
  have last : (output C.geometry C.hosts s).base+(output C.geometry C.hosts s).size≤C.self.base:=by
    apply le_trans _ r.selfAfter
    simpa [output,DescentResetOriginalSlots.bank,DescentResetOriginalSlots.offset,stop,DescentResetOriginalSlots.finish,
      Bank.size,DescentResetOriginalSlots.stride,Nat.add_assoc] using Nat.add_le_add_left fit C.geometry
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (last.trans_lt ((Nat.le_add_right ..).trans_lt (r.selfBank.2.2.trans_lt
    ((Nat.le_add_right ..).trans_lt (C.cut r))))),last⟩

theorem any (r : C.Room w) (m : Memory w) : (C.cpu w).Exec m (C.finalMem m) C.clock ∧ CheapCode (C.cpu w) ∧
    ∀i,i<C.base ∨ C.top≤ i→C.finalMem m i=m i:=by
  have broad:=C.cut r
  have below : C.self.base+C.hosts<2^w:=(Nat.add_le_add_left r.selfRows _).trans_lt (r.selfBank.2.2.trans_lt ((Nat.le_add_right ..).trans_lt broad))
  have origin : C.base≤C.self.base:=(Nat.le_add_right ..).trans (r.header.trans ((Nat.le_add_right ..).trans r.selfAfter))
  have gap:=DescentResetCompactGeometry.any C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts m r.here r.cnt r.header
    (r.selfAfter.trans_lt ((Nat.le_add_right ..).trans_lt below))
  have end_ (B : Bank) (fit : B.Fits w C.base) : B.Fits w C.self.base:=⟨fit.1,fit.2.1,fit.2.2.trans origin⟩
  have fits : C.pull.Fits w C.self.base:=⟨trivial,⟨end_ _ r.cnt,trivial⟩,⟨end_ _ r.ranks,C.shelf r 1,trivial⟩,trivial⟩
  let geo:=phase C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts w
  let walk:=scan w C.self.base C.hosts C.pull
  let publish:=DescentStaticWordColumn.program w C.broadcast C.lit C.size
  let g:=ticks C.inverse C.count C.base C.raw C.geometry C.hosts
  let s:=4+C.hosts*(2*C.pull.work+4)
  have ran : walk.Exec (C.first m) (C.second m) s :=
    @scan_exec w C.self.base C.hosts C.pull (C.first m) fits below
  have posted : publish.Exec (C.second m) (C.finalMem m) (4+10*C.size) :=
    @DescentStaticWordColumn.mount w C.broadcast C.size C.lit (C.second m) broad
  have both : (geo.seq walk).Exec m (C.second m) (g+s) :=
    @Procedure.Exec.then w geo walk m (C.first m) (C.second m) g s (@gap.1) (@ran)
  refine ⟨@Procedure.Exec.then w (geo.seq walk) publish m (C.second m) (C.finalMem m)
    (g+s) (4+10*C.size) (@both) (@posted),
    @cheap_seq w (geo.seq walk) publish
      (@cheap_seq w geo walk (@gap.2.1) (@scan_cheap w C.self.base C.hosts C.pull))
      (@DescentStaticWordColumn.cheap w C.broadcast C.lit C.size),?_⟩
  intro i outside
  have bcast:=r.selfBank.2.2
  have before : C.self.base+C.hosts≤C.broadcast:=(Nat.add_le_add_left r.selfRows _).trans bcast
  have bound : C.broadcast+C.size≤C.top:=by
    have known:=Nat.le_pow_clog (by decide : 1<2) (C.size+1)
    change _≤C.broadcast+2*(C.hosts*chunks C.groups C.lanes)+2^(Nat.clog 2 (C.size+1));omega
  have selfBroad : C.self.base ≤ C.broadcast := (Nat.le_add_right ..).trans bcast
  have broadTop : C.broadcast ≤ C.top := (Nat.le_add_right ..).trans bound
  calc
    C.finalMem m i = C.second m i := DescentStaticWordColumn.frame C.broadcast C.size C.lit
      (C.second m) i (outside.imp (·.trans_le (origin.trans selfBroad)) (bound.trans ·))
    _ = C.first m i := ProtocolRAMGeneratedWrite.frame_image C.self.base C.hosts C.pull
      (C.first m) i (outside.imp (·.trans_le origin) ((before.trans broadTop).trans ·))
    _ = m i := gap.2.2 i (outside.imp_right ((r.selfAfter.trans (selfBroad.trans broadTop)).trans ·))

set_option maxHeartbeats 1000000 in
def native (r : C.Room w) : NativePhase w := by
  have valid := C.any r (fun _ : ℕ => (0 : Word w))
  exact ⟨C.cpu w,C.clock,C.finalMem,@valid.2.1⟩

theorem runs (r : C.Room w) (m : Memory w) : (C.native r).Runs m := by
  have valid := C.any r m
  change (C.cpu w).Exec m (C.finalMem m) C.clock
  exact @valid.1

end Chart
end
end Hierarchy.DescentResetCompactGeometry

end OAI
