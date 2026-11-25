import OAI.Hierarchy.DescentTerminalAddressPlan
import OAI.Hierarchy.DescentTerminalRowArenaPrime
import OAI.Hierarchy.DescentTerminalEmitterParity

namespace OAI
/-! # One terminal address interval measured from the final dated history -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalRowArena DescentTerminalVertexFields
noncomputable section
set_option quotPrecheck false
variable {blocks : ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start oldPrivate:ℕ)
local notation "capacity" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
  (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)

def meter := MaskAllocation.counter (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) R start
local notation "C" => meter V R start
def registers := PrivateCounter.registers C oldPrivate S.sites capacity
def afterMeter := (C).base+capacity+S.sites+S.sites+3
local notation "base_" => afterMeter V S R start
def last := endAddress S I base_
local notation "O" => registers V S R start oldPrivate
local notation "L" => layout S I base_ O

theorem fits {bw:ℕ} (prior:∀f,(R.bank f).base+(R.bank f).size≤ start) (header:oldPrivate<start)
    (lower : Earlier S I base_ (C).layout bw) (end_ : last V S I R start<2^bw) :
    Home.Fits V S L C O bw := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base_
  have startLe:base_≤(rowArena S I base_).finish:=(rowArena S I base_).start_le _
  have room : base_<2^bw:=startLe.trans_lt (p0.trans_lt (p1.trans_lt (p2.trans_lt (p3.trans_lt (p4.trans_lt end_)))))
  have bounded:=MaskAllocation.room (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) R start prior room
  have starts : start≤(C).base:=Nat.le_add_right ..
  exact ⟨bounded,by change (C).base+capacity+S.sites+S.sites+3<_ at room;omega,
    PrivateCounter.registers_room C oldPrivate (header.trans_le starts) room,
    suffix_room S I base_ (C).layout O lower end_⟩

theorem meter_size :
    base_≤ start+(3*capacity+channels blocks+2*S.sites+3) := by
  have bill:=MaskAllocation.bill (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (blocks:=blocks)
  change start+_+capacity+S.sites+S.sites+3≤_
  omega

/-! The row parity service executes after the private scalar. Its two high output
bands extend the genuine scalar's memory to the entry point of the row plan. -/
def primeCode (bw:ℕ) := (rowArena S I base_).prime bw
variable {bw : ℕ}
def ready (m : Memory bw) := (rowArena S I base_).mount m
theorem prime_run (m : Memory bw) (end_ : last V S I R start<2^bw) :
    (primeCode V S I R start bw).Exec m (ready V S I R start m) (8+104*S.sites) ∧
      CheapCode (primeCode V S I R start bw) := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base_
  exact (rowArena S I base_).prime_run m
    (p0.trans_lt (p1.trans_lt (p2.trans_lt (p3.trans_lt (p4.trans_lt end_)))))

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
