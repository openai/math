import OAI.Hierarchy.DescentDatedActorHeaderTariff
import OAI.Hierarchy.DescentDatedActorGateTariff
import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! The whole native actor classifier, shape census and compact inverse share a single
four-column tariff. The dictionary is installed once per shape. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentStaticWordColumn DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
def actorFactor (v : ActorSetup) (degree cap : ℕ) :=
  v.headerFactor degree cap+2*v.directoryFactor+65536*(v.shapes+1)+1024*(v.shapes+2)

theorem actor_price (v : ActorSetup) (u : v.Inputs) (b w h : ℕ)
    (host : 0<v.hosts) (lanes : 0<v.lanes) (positive : 0<v.unitBits)
    (key : v.unitBits*v.lanes≤h/2) (load : u.stencil.work≤7) :
    v.actorTicks u b w+7*names (v.actorBody u b w) ≤
      v.actorFactor u.degree u.treeCap*ResetOutput.receiptArea h v.hosts v.chunksPerHost := by
  let H:=v.hosts
  let R:=v.chunksPerHost
  let Q:=v.shapes
  let A:=ResetOutput.receiptArea h H R
  let shelf:=(h+1)^3*2^(h/2)
  have head:=v.header_tariff u b w
  have census:=v.directory_tariff b w (v.scene b)
  have gate:=v.operator_price b u.population u.control u.query u.stencil w
  have one : 1≤ shelf := by change 0 < (h+1)^3*2^(h/2); positivity
  have range : R≤H*R := Nat.le_mul_of_pos_left _ host
  have small : 1+H+H*R≤A := by change 1+H+H*R≤H+H*R+shelf; omega
  have hst : H+1≤A := by omega
  have linear : 1+H+R+H*R≤2*A := by omega
  have sparse : shelf≤A := Nat.le_add_left ..
  have length : v.lanes≤h := (Nat.le_mul_of_pos_left v.lanes positive).trans (key.trans (Nat.div_le_self ..))
  have width : v.headerBits≤h/2 :=
    ((Nat.le_add_left v.headerBits _).trans (Nat.le_mul_of_pos_right v.unitBits lanes)).trans key
  have broadcast : (v.lanes+1)*2^v.headerBits≤ shelf := by
    change _ ≤(h+1)^3*2^(h/2)
    have poly : h+1≤(h+1)^3 := by nlinarith only [Nat.zero_le h,Nat.zero_le (h*h),Nat.zero_le (h*h*h)]
    exact Nat.mul_le_mul ((Nat.succ_le_succ length).trans poly) (Nat.pow_le_pow_right (by decide) width)
  have table : 2^(v.unitBits*v.lanes)≤ shelf :=
    (Nat.pow_le_pow_right (by decide) key).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have lookup : 1+(v.lanes+1)*2^v.headerBits+Q*2^(v.unitBits*v.lanes)≤(Q+2)*A := by
    have posted := Nat.mul_le_mul_left Q (table.trans sparse)
    have br:=broadcast.trans sparse
    have ar:=one.trans sparse
    calc
      _ ≤ Q*A+(A+A) := by omega
      _ = (Q+2)*A := by ring
  have classifier : v.operatorTime b u.population u.control u.query u.stencil w+
      7*names (v.operator b u.population u.control u.query u.stencil (w:=w)) ≤
      (65536*(Q+1))*A + (1024*(Q+2))*A := by
    calc
      _ ≤ 8192*(Q+1)*(u.stencil.work+1)*(1+H+H*R)+1024*(1+(v.lanes+1)*2^v.headerBits+
          Q*2^(v.unitBits*v.lanes)) := gate
      _ ≤ 8192*(Q+1)*8*A + 1024*((Q+2)*A) := by gcongr; omega
      _ = _ := by ring
  have collection := head.trans (Nat.mul_le_mul_left _ hst)
  have dense := census.trans (Nat.mul_le_mul_left _ linear)
  let term := DescentSharedBookScan.expr u.shared H u.degree u.treeCap
  change v.headerTime b u.depths term w+7*names (v.headers b u.depths term w) ≤
      v.headerFactor u.degree u.treeCap*A at collection
  change (v.directory b).ticks (v.scene b)+7*names ((v.directory b).program w (v.scene b)) ≤ v.directoryFactor*(2*A) at dense
  change _ ≤ v.actorFactor u.degree u.treeCap*A
  rw [actorBody,names_seq,names_seq,actorTicks,actorFactor]
  change (v.headerTime b u.depths term w+_)+_+7*((names (v.headers b u.depths term w)+_)+_)≤_
  dsimp only [Q] at classifier
  ring_nf at collection classifier dense ⊢
  omega

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
