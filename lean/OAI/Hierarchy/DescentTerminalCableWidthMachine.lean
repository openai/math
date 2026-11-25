import OAI.Hierarchy.DescentTerminalPeerMeasured
import OAI.Hierarchy.DescentTerminalWidthRowsRAM
import OAI.Hierarchy.DescentTerminalDenseHeaderBoot

namespace OAI
/-! # A single fixed RAM program from the original packed signed cables to the width tape -/
namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Rack (blocks cap groups M:ℕ) where
  sockets:Sockets
  homes:ℕ
  degree:ℕ
  cellBits:ℕ
  scale:ℕ
  maxRows:ℕ
  cables:Fin blocks→Fin (2*cap)→Bank
  lanes:0<M

namespace Rack
variable {blocks cap groups M w:ℕ} (T:Rack blocks cap groups M)
def tickets:=T.homes*T.degree
def base:=T.sockets.stop T.homes T.degree
abbrev cols (_ : Rack blocks cap groups M) := columns blocks cap groups M
def readCols:=source (groups:=groups) (M:=M) (T.sockets.first T.homes T.degree)
  (T.sockets.ticket T.homes T.degree) T.cables
def passes:=Gather.reads T.base T.tickets T.readCols
def slab:=Gather.rom T.base T.cols T.tickets
def population:Bank:=⟨T.slab+DescentTerminalPointerFrame.size T.cols T.cellBits,Nat.clog 2 T.tickets⟩
def printer:DescentTerminalWidthRowsRAM.Layout:=
  ⟨T.population.base+T.population.size,T.tickets,T.maxRows,groups*(blocks*cap)*T.scale,T.population⟩
def gates:=aggregate (blocks:=blocks) (cap:=cap) (groups:=groups) (d:=T.cellBits) T.degree T.scale T.lanes
def middle (w:ℕ) := (ProtocolRAM.program w T.passes).seq
  (DescentTerminalPointerFrame.program w T.slab (Gather.banks (L:=T.cols) T.base T.tickets) T.tickets T.gates)
def program (w q p:ℕ):=((T.sockets.prepare T.homes T.degree w (chunks groups M)).seq (T.middle w)).seq (T.printer.program q p w)
def boot (m:Memory w) :=T.sockets.ready T.homes T.degree (chunks groups M) m
def counters (m:Memory w) :=DescentTerminalPointerFrame.result T.slab (Gather.banks (L:=T.cols) T.base T.tickets)
  T.tickets T.gates (result T.passes (T.boot m))
def final (q p:ℕ) (m:Memory w) :=T.printer.finalMem q p w (T.counters m)
def fee:=DescentTerminalPointerFrame.size T.cols T.cellBits
def middleTime:=clock T.passes+((4+10*T.fee)+(4+T.tickets*(16+26*T.cols)))
def time (q p:ℕ) := (4+10*(3*(T.sockets.home T.homes T.degree).size)+T.middleTime)+T.printer.clocks q p

/-- Only prior columns and the ceiling on the actual new memory are required.
Every new bank's base is determined by the previous bank's rounded width. -/
structure Fits (w:ℕ) : Prop where
  prior:∀x j,(T.cables x j).Fits w T.sockets.origin
  roster:T.sockets.roster.Fits w T.sockets.origin
  digit:2^T.cellBits<2^w
  space:T.printer.stop<2^w

theorem gaps :
    T.sockets.origin≤T.base ∧ T.base≤T.slab ∧ T.population.base+T.tickets≤T.printer.origin ∧
      T.printer.origin≤T.printer.stop := by
  have cover:T.tickets≤T.population.size:=Nat.le_pow_clog (by decide) _
  refine ⟨Nat.le_add_right ..,?_,Nat.add_le_add_left cover _,?_⟩
  · exact (Nat.le_add_right T.base (T.cols*T.tickets)).trans (Nat.le_add_right ..)
  · change T.printer.origin≤T.printer.sink+1+T.printer.groups+T.printer.groups
    have e:=Nat.le_add_right T.printer.origin T.printer.entries
    have f:=Nat.le_add_right T.printer.prefix.base T.printer.prefix.size
    have h:=Nat.le_add_right T.printer.output.base T.printer.output.size
    change T.printer.origin≤T.printer.prefix.base at e
    change T.printer.prefix.base≤T.printer.output.base at f
    change T.printer.output.base≤T.printer.sink at h
    omega

theorem read_room (fit:T.Fits w) : ∀j,(T.readCols j).Fits w T.base := by
  have gaps:=T.gaps
  have end_:T.base<2^w:=by
    have bound:T.slab≤T.population.base:=Nat.le_add_right ..
    have outer:T.population.base≤T.printer.origin:=by omega
    exact gaps.2.1.trans_lt (bound.trans_lt (outer.trans_lt (gaps.2.2.2.trans_lt fit.space)))
  have room (b:Bank) (endPos:b.base+b.size≤T.base):b.Fits w T.base:=
    ⟨Nat.two_pow_pos _,by omega,endPos⟩
  have first:(T.sockets.home T.homes T.degree).Fits w T.base:=room _ (by
    change T.sockets.origin+(T.sockets.home T.homes T.degree).size≤T.sockets.origin+3*(T.sockets.home T.homes T.degree).size
    omega)
  have lane:(T.sockets.lane T.homes T.degree).Fits w T.base:=room _ (by
    change T.sockets.origin+(T.sockets.home T.homes T.degree).size+(T.sockets.home T.homes T.degree).size≤T.sockets.origin+3*(T.sockets.home T.homes T.degree).size
    omega)
  have head:(T.sockets.head T.homes T.degree).Fits w T.base:=room _ (by
    change T.sockets.origin+2*(T.sockets.home T.homes T.degree).size+(T.sockets.home T.homes T.degree).size≤T.sockets.origin+3*(T.sockets.home T.homes T.degree).size
    omega)
  have prev:=room T.sockets.roster (fit.roster.2.2.trans gaps.1)
  intro j
  unfold readCols source
  cases (number blocks cap groups M).symm j with
  | inl _=>exact ⟨⟨prev,trivial⟩,trivial,⟨⟨prev,trivial⟩,⟨first,trivial⟩,trivial,⟨lane,trivial⟩⟩,trivial⟩
  | inr u=>exact ⟨room _ ((fit.prior u.1 u.2.1).2.2.trans gaps.1),⟨⟨head,trivial⟩,trivial⟩⟩

theorem run (q p:ℕ) (m:Memory w) (fit:T.Fits w) :
    (T.program w q p).Exec m (T.final q p m) (T.time q p) ∧ CheapCode (T.program w q p) ∧
    (∀j:Fin T.tickets,T.counters m (T.population.base+j.val)=((T.gates (Gather.values T.readCols (T.boot m) j)).val:Word w)) ∧
    ∀a,a<T.sockets.origin→T.final q p m a=m a := by
  have gaps:=T.gaps
  have bound:T.slab≤T.population.base:=Nat.le_add_right ..
  have middleBound:T.population.base+T.tickets<2^w:=gaps.2.2.1.trans_lt (gaps.2.2.2.trans_lt fit.space)
  have low:T.base<2^w:=by omega
  have start:=T.sockets.mount T.homes T.degree (chunks groups M) m low
  have counts:=issue (groups:=groups) (d:=T.cellBits) T.degree T.scale T.lanes T.base T.tickets
    (T.sockets.first T.homes T.degree) (T.sockets.ticket T.homes T.degree) T.cables (T.boot m) (T.read_room fit) fit.digit middleBound
  have sourceFit:T.population.Fits w T.printer.origin:=⟨Nat.two_pow_pos _,by
    have outer:T.population.base+T.population.size<2^w:=gaps.2.2.2.trans_lt fit.space
    omega,le_rfl⟩
  have tail:=T.printer.exec_any q p w (T.counters m) sourceFit fit.space
  let initial := T.sockets.prepare T.homes T.degree w (chunks groups M)
  refine ⟨?_,?_,?_,?_⟩
  · have throughCounters := @Procedure.Exec.then w initial (T.middle w) m (T.boot m) (T.counters m)
      _ _ start.1 counts.1
    exact @Procedure.Exec.then w (initial.seq (T.middle w)) (T.printer.program q p w) m (T.counters m)
      (T.final q p m) _ _ throughCounters tail.1
  · exact @cheap_seq w (initial.seq (T.middle w)) (T.printer.program q p w)
      (@cheap_seq w initial (T.middle w) start.2.1 counts.2.1) tail.2
  · exact counts.2.2.1
  · intro a ha
    have early:a<T.printer.origin:=by omega
    exact (T.printer.frame_any q p w (T.counters m) sourceFit fit.space a (.inl early)).trans
      ((counts.2.2.2 a (.inl (ha.trans_le gaps.1))).trans (start.2.2 a ha))

end Rack
end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
