import OAI.Hierarchy.DescentPhysicalResetActors
import OAI.Hierarchy.DescentSharedBookTariff

namespace OAI
/-! The scalar depth and common-book passes, three literal header pages,
and the dense census and inverse directory all reuse the original host set. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentSIMDLookup DescentStaticWordColumn DescentOrdinaryDestRAM ProtocolRAM
open DescentPackedColony.Phase.Arena DescentResetNewActorDirectory
noncomputable section

private theorem rounded (n : ℕ) : 2^Nat.clog 2 n ≤ 2*n+1 := by
  by_cases small : n≤1
  · interval_cases n <;> decide
  have low := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
  have pos := Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
  cases eqn : Nat.clog 2 n with
  | zero => omega
  | succ j => rw [eqn] at low; simp only [Nat.pred_succ] at low; rw [Nat.pow_succ]; omega

private theorem times_row (n : ℕ) : (times n .row).work=1+3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [times,Expr.work,ih,Nat.mul_succ]; omega

def scoreBound (degree cap : ℕ) := 10000*(degree+1)^2*(cap+1)

theorem common_work {v : ActorSetup} (u : ActorSetup.Inputs v) : (DescentSharedBookScan.expr u.shared v.hosts u.degree u.treeCap).work ≤
    scoreBound u.degree u.treeCap := by
  let term := DescentSharedBookScan.expr u.shared v.hosts u.degree u.treeCap
  have h := DescentSharedBookScan.shared_work u.shared u.degree u.treeCap v.hosts 0
  change term.work+1+term.work+1+1≤ scoreBound u.degree u.treeCap at h
  change term.work≤_
  omega

def headerFactor (v : ActorSetup) (degree cap : ℕ) :=
  4096*(1+v.oldWidth+v.maxCount+(v.arity+1)*(scoreBound degree cap+1))

theorem header_tariff (v : ActorSetup) (u : v.Inputs) (b w : ℕ) :
    let term := DescentSharedBookScan.expr u.shared v.hosts u.degree u.treeCap
    v.headerTime b u.depths term w+7*names (v.headers b u.depths term w) ≤
      v.headerFactor u.degree u.treeCap*(v.hosts+1) := by
  intro term
  have dep : (v.depthExpr u.depths).work=1+3*(v.oldWidth+1)+5 := by
    change (times (v.oldWidth+1) .row).work+5=_
    rw [times_row]
  have words : (v.constants b (w:=w)).length ≤ 2*v.hosts+2*(v.oldWidth+1)+2*(v.maxCount+1)+3 := by
    have ha:=rounded v.hosts
    have hb:=rounded (v.oldWidth+1)
    have hc:=rounded (v.maxCount+1)
    dsimp only [constants,Image.length,starts,levels,heights,next,bank,Bank.size]
    omega
  have score : term.work≤ scoreBound u.degree u.treeCap := common_work u
  have hw := (v.constants b (w:=w)).hardware.2
  rw [headers,names_seq,names_seq,names_scan,names_scan,hw,headerTime,dep]
  calc
    _ ≤ ((4+v.hosts*(2*(1+3*(v.oldWidth+1)+5)+4))+
         (4+v.hosts*v.arity*(2*scoreBound u.degree u.treeCap+4)))+
        (4+10*(2*v.hosts+2*(v.oldWidth+1)+2*(v.maxCount+1)+3))+
        7*((11+4*(1+3*(v.oldWidth+1)+5))+(11+4*scoreBound u.degree u.treeCap)+
          15*((2*v.hosts+2*(v.oldWidth+1)+2*(v.maxCount+1)+3)+1)) := by gcongr
    _ ≤ _ := by unfold headerFactor; ring_nf; omega

def directoryFactor (v : ActorSetup) :=
  (8192+7*Layout.fixedScatter)*(v.shapes+1)

theorem directory_tariff (v : ActorSetup) (b w : ℕ) (src : Bank) :
    (v.directory b).ticks src+7*names ((v.directory b).program w src) ≤
      v.directoryFactor*(1+v.hosts+v.chunksPerHost+v.hosts*v.chunksPerHost) := by
  rw [Layout.exact_time,Layout.exact_names]
  dsimp only [directory,Layout.sites]
  unfold directoryFactor
  ring_nf
  omega

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
