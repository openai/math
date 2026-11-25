import OAI.Hierarchy.ProtocolRAMCalendarHardware
import OAI.Hierarchy.ProtocolRAMCalendarCost
import OAI.Hierarchy.ProtocolRAMPurchaseStageTime

namespace OAI
/-! # The post-purchase controller's clock and text for bounded local expressions -/
namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage

private theorem mappedSum {α : Type*} (as : List α) (f : α→ℕ) (K : ℕ) (bound : ∀x∈as,f x≤K) :
    (as.map f).sum≤as.length*K := by
  induction as with
  | nil=>simp
  | cons a as ih=>
    change f a+(as.map f).sum≤(as.length+1)*K
    calc
      f a+(as.map f).sum≤K+as.length*K:=
        Nat.add_le_add (bound a (List.mem_cons_self ..)) (ih (fun x hx=>bound x (List.mem_cons_of_mem _ hx)))
      _=(as.length+1)*K:=by rw [Nat.succ_mul,Nat.add_comm]

def postClockCap (U K : ℕ) :=
  3*(4+(U+1)*(42+2*K))+2*(4+U*(2*K+4))+(19+11*U)+
    (4+(17+4*U)*(4+U*(2*K+4)))+28

def postTextCap (U K : ℕ) :=
  3*(11+4*(19+K))+2*(11+4*K)+15+21+15+(17+4*U)*(11+4*K)+(11+4*10)

theorem post_bounds_of_work {q d : ℕ} (U K : ℕ) (L : Dispatch) (B : Repair q d)
    (ports : d≤U) (quotes : B.batch.quotes.length≤U) (work : ∀p∈writes L B,p.term.work≤K)
    (mask : (repairMask B).work≤K) (invalid : (invalidExpr (enabledBatch L B)).work≤K)
    (excess : B.tests.excess.term.work≤K) (payload : B.tests.payload.term.work≤K) (disc : B.tests.discrepancy.term.work≤K) :
    postFactor B L U≤postClockCap U K ∧ postText L B≤postTextCap U K := by
  have length : (writes L B).length≤17+4*U:=by rw [writes_length];omega
  have pf (t : Expr) (ht : t.work≤K) : 4+U*(2*t.work+4)≤4+U*(2*K+4) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left U (by omega)) _
  have cf (z : AttemptGate.Check) (hz : z.term.work≤K) :
      checkFactor U z≤4+(U+1)*(42+2*K) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have unit : ((writes L B).map (passFactor U)).sum≤(17+4*U)*(4+U*(2*K+4)) :=
    (mappedSum (writes L B) _ _ (fun p hp=>pf _ (work p hp))).trans (Nat.mul_le_mul_right _ length)
  have tex : ((writes L B).map (fun p=>rowText p.term)).sum≤(17+4*U)*(11+4*K) :=
    (mappedSum (writes L B) _ _ (fun p hp=>show rowText p.term≤11+4*K by
      have small:=work p hp
      unfold rowText
      omega)).trans (Nat.mul_le_mul_right _ length)
  have a:=cf _ excess
  have b:=cf _ payload
  have c:=cf _ disc
  have m:=pf _ mask
  have i:=pf _ invalid
  constructor
  · simp only [postFactor,postClockCap,verdict_work]
    omega
  · simp only [postText,postTextCap,verdict_work,listText,checkText,rowText] at tex ⊢
    omega

theorem post_resources_of_work (U K : ℕ) : ∃C,∀{q d h : ℕ}(L : Dispatch)(B : Repair q d),
    d≤U → B.batch.quotes.length≤U → (∀p∈writes L B,p.term.work≤K) →
    (repairMask B).work≤K → (invalidExpr (enabledBatch L B)).work≤K →
    B.tests.excess.term.work≤K → B.tests.payload.term.work≤K → B.tests.discrepancy.term.work≤K →
    L.candidates≤2^h*U → B.tests.excess.rows≤2^h*U → B.tests.payload.rows≤2^h*U →
    B.tests.discrepancy.rows≤2^h*U → postTicks L B≤C*2^h ∧ postText L B≤C := by
  refine ⟨max (postClockCap U K) (postTextCap U K),?_⟩
  intro q d h L B ports quotes work mask invalid excess payload disc candidates xs ys zs
  have bound:=post_bounds_of_work U K L B ports quotes work mask invalid excess payload disc
  have bill:=post_bill B L (2^h) U (Nat.two_pow_pos _) candidates xs ys zs
    (fun p hp=>(write_rows L B hp).le.trans candidates)
  exact ⟨bill.trans ((Nat.mul_le_mul_left _ (bound.1.trans (le_max_left ..))).trans_eq (Nat.mul_comm ..)),
    bound.2.trans (le_max_right ..)⟩

end Hierarchy.ProtocolRAM.Calendar

end OAI
