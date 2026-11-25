import OAI.Optimization.LinearProgramming.Compression.CallableQueryBound
import OAI.Optimization.LinearProgramming.PrimalDual.RAMBudget
import OAI.Optimization.LinearProgramming.RAM.Array

/-! The uniform reentrant reset capacity is computed by actual address arithmetic.
No dimensions, precision-dependent capacities or return addresses are runtime code literals. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM RAM.Tape
open scoped BigOperators

/-- Saturating subtraction implements a maximum without a new RAM operation. -/
def maxAddressTerm {r : ℕ} (a b : AddressTerm r) : AddressTerm r := a+(b-a)

@[simp] theorem maxAddressTerm_value {r : ℕ} (a b : AddressTerm r) (env : Fin r → ℕ) :
    (maxAddressTerm a b).value env=max (a.value env) (b.value env) := by
  change a.value env+(b.value env-a.value env)=max _ _
  omega

/-- A fixed expression takes the term count and cutoff fuel from any two address
expressions in the calling header. A guarded scan can reuse this capacity for each row. -/
def reentrantQueryCapTerm {r : ℕ} (n fuel : AddressTerm r) : AddressTerm r :=
  let token := 2*(2*fuel+3)+3+n*(2*(fuel+3)+3)
  let width := 3*token+n+16
  let time := maxAddressTerm (9*(n+1)+6) (30*token+9)
  maxAddressTerm (.val fixedProxyAddressBudget) (width*width) + time

@[simp] theorem reentrantQueryCapTerm_value {r : ℕ} (n fuel : AddressTerm r) (env : Fin r → ℕ) :
    (reentrantQueryCapTerm n fuel).value env = reentrantQueryCap (n.value env) (fuel.value env) := by
  change (maxAddressTerm _ _).value env + (maxAddressTerm _ _).value env = _
  rw [maxAddressTerm_value,maxAddressTerm_value]
  simp only [reentrantQueryCap,preparedProxyRawSpan,preparedTokenBudget,proxyQuerySteps,AddressTerm.value,
    AddressOp.value,pow_two]
  rfl

/-- A logical block computing the exact capacity and writing its one-past endpoint
for the reset loop. The expression compiler uses the supplied high scratch base. -/
def queryCapacityBlock {r : ℕ} (n fuel : AddressTerm r) (scratch : ℕ) : Block :=
  .seq ((reentrantQueryCapTerm n fuel+1).code scratch) (.op (.addrCopy 60 scratch))

theorem queryCapacityBlock_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r : ℕ} (n fuel : AddressTerm r) (env : Fin r→ℕ) (scratch size : ℕ) (m : Memory K)
    (P : K → Prop) (hs : m.AllData P) (hr : r≤scratch) (hinput : ∀ i : Fin r,m.index i=env i)
    (hsize : ∀ i,env i≤size) :
    ∃ k t, Block.Eval (Memory.AllData P) (queryCapacityBlock n fuel scratch) m k t ∧
      k≤(reentrantQueryCapTerm n fuel+1).boundCost.eval size+1 ∧ t.data=m.data ∧
      t.index 60=reentrantQueryCap (n.value env) (fuel.value env)+1 ∧
      ∀ i<scratch,i≠60 → t.index i=m.index i := by
  let e := reentrantQueryCapTerm n fuel+1
  obtain ⟨j,u,body,hj,data,low,out⟩ := e.correct env scratch m hr hinput hs
  let t := u.putIndex 60 (u.index scratch)
  have copy : Block.Eval (Memory.AllData P) (.op (.addrCopy 60 scratch)) u 1 t := eval_copyI u body.safe_end _ _
  have hresult : u.index scratch=reentrantQueryCap (n.value env) (fuel.value env)+1 := by
    rw [← reentrantQueryCapTerm_value n fuel env]
    exact out
  refine ⟨j+1,t,body.seq copy,Nat.add_le_add_right (hj.trans (e.cost_le env size hsize)) 1,data,?_,?_⟩
  · simpa only [t,Memory.putIndex_same] using hresult
  · intro i hi h60
    exact (Memory.putIndex_ne u h60 (u.index scratch)).trans (low i hi)

end Compression
end LinearProgramming
end Optimization
end OAI
