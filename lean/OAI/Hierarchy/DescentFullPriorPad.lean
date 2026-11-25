import OAI.Hierarchy.DescentDatePortArchiveFits
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentPriorNodePresence
import OAI.Hierarchy.DescentResetHostPadRegisters
import OAI.Hierarchy.DescentResetPriorHostPadRead

namespace OAI
/-! # Host padding followed by the two true node columns at a reset entrance -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentSIMDLookup DescentResetPriorHostPad ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (p : DatePorts) (k base : ℕ)
local notation "P" => p.resetPad k
local notation "C" => p.presence k
local notation "mid" => (P).endAddress base

def arityIndex (x : Fin (2^k)) : Fin (P).dataRect.pages :=
  finProdFinEquiv ((⟨1,by omega⟩ : Fin (2+7*p.argumentsPerNode)),x)
def paddedArity (x : Fin (2^k)) : Bank :=(P).operandBank base (p.arityIndex k x)
def fullPad (src : Fin (P).dataRect.pages→Bank) (role : Fin (2^k)→Bank) (w : ℕ) : NativePhase w :=
  ((P).phase base src role w).seq ((C).phase mid ((P).roleBank base) (p.paddedArity k base) w)

theorem pad_order : base≤ mid ∧ mid≤p.priorStart k base:=
  ⟨((P).cuts base).1.trans ((P).cuts base).2,by
    have s:=(C).starts mid
    exact s.1.trans (s.2.1.trans (s.2.2.1.trans s.2.2.2))⟩

theorem pad_headers {w : ℕ} (fit : mid<2^w) (x : Fin (2^k)) :
    ((P).roleBank base x).Fits w mid ∧ (p.paddedArity k base x).Fits w mid:=
  ⟨((P).role_fit base fit x).1,((P).operand_fit base fit (p.arityIndex k x)).1⟩

theorem full_pad_any {w : ℕ} (src : Fin (P).dataRect.pages→Bank) (role : Fin (2^k)→Bank)
    (m : Memory w) (old : ∀j,(src j).Fits w base) (tokens : ∀x,(role x).Fits w base)
    (room : p.priorStart k base<2^w) :
    (p.fullPad k base src role w).Runs m ∧ ∀i,i<base ∨ p.priorStart k base≤ i →
      (p.fullPad k base src role w).image m i=m i:=by
  have cuts:=p.pad_order k base
  have fit:=cuts.2.trans_lt room
  have a:=(P).any base src role m old tokens fit
  let temp:=((P).phase base src role w).image m
  have b:=(C).any mid ((P).roleBank base) (p.paddedArity k base) temp (p.pad_headers k base fit) room
  refine ⟨NativePhase.seq_runs _ _ _ a.1 b.1,?_⟩
  intro i outside
  exact (b.2 i (outside.imp (fun l=>l.trans_le cuts.1) id)).trans
    (a.2 i (outside.imp id (fun right=>cuts.2.trans right)))

open DescentOrdinaryHostPad DescentPackedColony
theorem full_pad_reads {w : ℕ} (src : Fin (P).dataRect.pages→Bank) (role : Fin (2^k)→Bank)
    (m : Memory w) (old : ∀j,(src j).Fits w base) (registered : ∀x,(role x).Fits w base)
    (room : p.priorStart k base<2^w) (live : 0<p.roleLanes)
    (data_ : Fin (P).dataRect.pages→Fin p.operandHosts→Fin p.venue.groups→Cell (p.operandBits*p.nodes))
    (role_ : Fin (2^k)→Fin p.operandHosts→Fin p.venue.groups→Cell (p.tokenBits*p.nodes))
    (actual : ∀j,p.operandHosts*chunks p.venue.groups p.operandLanes≤(src j).size ∧ Reads (src j) (data_ j) p.operandLanes m)
    (labels : ∀j,p.operandHosts*chunks p.venue.groups p.roleLanes≤(role j).size ∧ Reads (role j) (role_ j) p.roleLanes m) :
    let after:=(p.fullPad k base src role w).image m
    (∀f x,Reads ((C).bank mid f x) (if f=0 then fun h g=>(C).readings (extend p.venue.hosts (role_ x) h g)
        else extend p.venue.hosts (data_ (p.arityIndex k x))) p.operandLanes after) ∧
      (∀j,Reads ((P).operandBank base j) (extend p.venue.hosts (data_ j)) p.operandLanes after) ∧
      ∀x,Reads ((P).roleBank base x) (extend p.venue.hosts (role_ x)) p.roleLanes after:=by
  intro after
  have fit:mid<2^w:=(p.pad_order k base).2.trans_lt room
  let temp:=((P).phase base src role w).image m
  have fresh:=(P).issued base src role m old registered fit data_ role_ actual labels
  have high:=(C).any mid ((P).roleBank base) (p.paddedArity k base) temp (p.pad_headers k base fit) room
  refine ⟨(C).issued mid ((P).roleBank base) (p.paddedArity k base) temp (p.pad_headers k base fit) room
    live (fun x=>extend _ (role_ x)) (fun x=>extend _ (data_ (p.arityIndex k x)))
    (fun x=>⟨((P).role_fit base fit x).2,((P).operand_fit base fit (p.arityIndex k x)).2⟩)
    (fun x=>⟨fresh.2 x,fresh.1 (p.arityIndex k x)⟩),?_,?_⟩
  · intro j row_
    have bank:=(P).operand_fit base fit j
    exact (high.2 _ (.inl ((Nat.add_lt_add_left ((row _ _ _ row_).isLt.trans_le bank.2) _).trans_le bank.1.2.2))).trans (fresh.1 j row_)
  · intro x row_
    have bank:=(P).role_fit base fit x
    exact (high.2 _ (.inl ((Nat.add_lt_add_left ((row _ _ _ row_).isLt.trans_le bank.2) _).trans_le bank.1.2.2))).trans (fresh.2 x row_)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
