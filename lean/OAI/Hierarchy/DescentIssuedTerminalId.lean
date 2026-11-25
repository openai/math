import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentResetCableSlots
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPortFlowRAM

namespace OAI
/-! # Measured terminal ordinals in the sparse public cable directory -/

namespace Hierarchy.DescentIssuedTerminalId
open DescentContacts DescentHostDirectory DescentResetCableSlots
open ThreeFlat.RAM DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {V F : Type} [Fintype V] {w Y k H : ℕ}

def heap (x : ℕ×ℕ) := 2^x.1+x.2

theorem heap_range (d i : ℕ) (leg : i<2^d) : 2^d≤heap (d,i) ∧ heap (d,i)<2^(d+1) := by
  unfold heap
  rw [pow_succ];simp only
  omega

theorem heap_injective {x y : ℕ×ℕ} (a : x.2<2^x.1) (b : y.2<2^y.1) (eqn : heap x=heap y) : x=y := by
  have ax : 2^x.1≤heap x ∧ heap x<2^(x.1+1) := heap_range x.1 x.2 a
  have ay : 2^y.1≤heap y ∧ heap y<2^(y.1+1) := heap_range y.1 y.2 b
  have d : x.1=y.1 := by
    rcases lt_trichotomy x.1 y.1 with lt|same|gt
    · have le : 2^(x.1+1)≤2^y.1 := Nat.pow_le_pow_right (by decide) lt
      exact False.elim (((ax.2.trans_le le).trans_le ay.1).ne eqn)
    · exact same
    · have le : 2^(y.1+1)≤2^x.1 := Nat.pow_le_pow_right (by decide) gt
      exact False.elim (((ay.2.trans_le le).trans_le ax.1).ne eqn.symm)
  exact Prod.ext d (by unfold heap at eqn;rw [d] at eqn;omega)

/-- The public tree-interval code is installed once per depth budget, including the
padding word at zero. Its order agrees with the existing compact directory. -/
def intervalData (k a : ℕ) :=
  if hit : ∃p : ↥(codes k),p.val.2<2^p.val.1 ∧ heap p.val=a then (interval k hit.choose).val else 0

theorem interval_read (d i : ℕ) (small : d≤k) (id : i<2^d) :
    intervalData k (2^d+i)=(interval k ⟨(d,i),mem_codes small id⟩).val := by
  let p : ↥(codes k):=⟨(d,i),mem_codes small id⟩
  have hit : ∃q : ↥(codes k),q.val.2<2^q.val.1 ∧ heap q.val=2^d+i := ⟨p,id,rfl⟩
  have unique : hit.choose=p := Subtype.ext (heap_injective hit.choose_spec.1 id hit.choose_spec.2)
  simp [intervalData,hit,unique,p]

def prefixData (k Y v : ℕ) := v*(2^(k+1)*(Y+1))

omit [Fintype V] in
theorem «fields» {n : ℕ} (host : V↪Fin H) (code : F↪V×Endpoint (2^n))
    (valid : ∀t,(code t).2.1.1≤k ∧ (code t).2.1.2<2^(code t).2.1.1) (t : F) :
    (terminal host code valid t).val=
      prefixData k (2^n) (host (code t).1).val+
      (2^n+1)*intervalData k (heap (code t).2.1)+(DescentResetCableSlots.optional (code t).2.2).val := by
  let p : ↥(codes k) := ⟨(code t).2.1,mem_codes (valid t).1 (valid t).2⟩
  have read : intervalData k (heap (code t).2.1)=(interval k p).val :=
    interval_read _ _ (valid t).1 (valid t).2
  rw [read]
  change (DescentResetCableSlots.optional (code t).2.2).val+(2^n+1)*(interval k p).val+
    (2^(k+1)*(2^n+1))*(host (code t).1).val=_
  unfold prefixData
  ring

structure Banks where
  hostBase : Bank
  powers : Bank
  intervals : Bank

def tag (S : Banks) (Y : ℕ) (host depth id opt : Expr) :=
  let interval:=Expr.lookup S.intervals (.op .add (.lookup S.powers depth) id)
  Expr.op .add (.op .add (.lookup S.hostBase host) (DescentPortFlow.scale interval (Y+1))) opt

theorem tag_read (S : Banks) (m : Memory w) (r : Word w) (h d i z : Expr)
    (actor depth id opt : ℕ) (small : depth≤k) (legal : id<2^depth)
    (hostFit : actor<S.hostBase.size) (df : depth<S.powers.size) (ifit : 2^(k+1)≤S.intervals.size)
    (wide : ∀a∈[S.hostBase,S.powers,S.intervals],a.size<2^w)
    (hR : h.eval m r=(actor:Word w)) (dR : d.eval m r=(depth:Word w))
    (iR : i.eval m r=(id:Word w)) (zR : z.eval m r=(opt:Word w))
    («prefix» : m (S.hostBase.base+actor)=(prefixData k Y actor:Word w))
    (power : m (S.powers.base+depth)=((2^depth:ℕ):Word w))
    (idx : m (S.intervals.base+(2^depth+id))=(intervalData k (2^depth+id):Word w)) :
    (tag S Y h d i z).eval m r=((prefixData k Y actor+(Y+1)*intervalData k (2^depth+id)+opt:ℕ):Word w) := by
  have a : 2^depth+id<2^(k+1) := (heap_range depth id legal).2.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ small))
  have hr := (lookup_nat S.hostBase m r h actor hR hostFit (wide _ (by simp))).trans «prefix»
  have dr := (lookup_nat S.powers m r d depth dR df (wide _ (by simp))).trans power
  have idxRead : (Expr.op .add (.lookup S.powers d) i).eval m r=((2^depth+id:ℕ):Word w) := by
    change (Expr.lookup S.powers d).eval m r+i.eval m r=_
    rw [dr,iR,Nat.cast_add]
  have ir:=(lookup_nat S.intervals m r _ _ idxRead (a.trans_le ifit) (wide _ (by simp))).trans idx
  change (Expr.lookup S.hostBase h).eval m r+
    (DescentPortFlow.scale (.lookup S.intervals _) (Y+1)).eval m r+z.eval m r=_
  rw [hr,DescentPortFlow.scale_eval,ir,zR]
  push_cast;ring

end
end Hierarchy.DescentIssuedTerminalId

end OAI
