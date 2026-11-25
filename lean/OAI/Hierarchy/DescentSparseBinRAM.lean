import OAI.Hierarchy.DescentPhysicalOrder
import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap

namespace OAI
/-! # Stable native sorting within one bounded destination aperture

The machine ranks installed destination tags using their measured RAM words and
breaks ties by original aperture slot. Each call permutes one authentic column,
including absolute starts in the shared old-edge tape. -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing BigOperators
variable {n w : ℕ}

def before (key : Fin n→ℕ) (j i : Fin n) := key j<key i ∨ key j=key i ∧ j < i

private theorem serial_lt (key : Fin n→ℕ) (j i : Fin n) :
    key j*n+j.val<key i*n+i.val ↔ before key j i := by
  have lesser (a b : Fin n) (h : key a<key b) : key a*n+a.val<key b*n+b.val := by
    have mul := Nat.mul_le_mul_right n (show key a+1≤key b from h)
    rw [Nat.add_mul,one_mul] at mul
    have bound := a.isLt
    omega
  rcases lt_trichotomy (key j) (key i) with lo|eqn|hi
  · exact ⟨fun _=>Or.inl lo,fun _=>lesser j i lo⟩
  · simp [eqn,before]
  · exact ⟨fun h=>(lesser i j hi).not_gt h |>.elim,
      fun h=>h.elim (fun q=>(hi.not_gt q).elim) (fun q=>(hi.ne q.1.symm).elim)⟩

def serial (key : Fin n→ℕ) : Fin n ↪ ℕ where
  toFun i := key i*n+i.val
  inj' := by
    intro i j eqn
    by_contra ne
    have neither : ¬before key i j ∧ ¬before key j i :=
      ⟨fun h=>(serial_lt key i j).mpr h |>.ne eqn,
       fun h=>(serial_lt key j i).mpr h |>.ne eqn.symm⟩
    rcases lt_trichotomy (key i) (key j) with l|e|r
    · exact neither.1 (.inl l)
    · rcases lt_or_gt_of_ne ne with a|a
      · exact neither.1 (.inr ⟨e,a⟩)
      · exact neither.2 (.inr ⟨e.symm,a⟩)
    · exact neither.2 (.inl r)

def order (key : Fin n→ℕ) : Equiv.Perm (Fin n) :=
  (DescentPhysicalOrder.physical (serial key)).trans (finCongr (Fintype.card_fin _))

theorem order_val (key : Fin n→ℕ) (i : Fin n) :
    (order key i).val=(Finset.univ.filter (fun j=>before key j i)).card := by
  change (DescentPhysicalOrder.physical (serial key) i).val=_
  rw [DescentPhysicalOrder.physical_val]
  apply congrArg Finset.card
  exact Finset.filter_congr (fun j _ => serial_lt key j i)

/-- The local comparison is lexicographic without multiplying the measured
tag by the aperture size, so the packed product need not fit a word. -/
def indicator (keys : Bank) (j : Fin n) : Expr :=
  let lhs := Expr.lookup keys (.lit j.val)
  let rhs := Expr.lookup keys .row
  .branch .lt lhs rhs (.lit 1)
    (.branch .eq lhs rhs (.branch .lt (.lit j.val) .row (.lit 1) (.lit 0)) (.lit 0))

def rankExpr (n : ℕ) (keys : Bank) := DescentGLScoreRAM.sumExpr n (indicator keys)

private theorem lookup (keys : Bank) (i : Fin n) (m : Memory w) (hn : n≤keys.size)
    (hw : keys.size<2^w) : keys.read m (i.val:Word w)=m (keys.base+i.val) := by
  have small := i.isLt.trans_le hn
  simp [Bank.read,Fin.val_cast_of_lt (small.trans hw),Nat.mod_eq_of_lt small]

private theorem branch_lt (x y yes no : Expr) (m : Memory w) (row : Word w) :
    (Expr.branch .lt x y yes no).eval m row =
      if (x.eval m row).val < (y.eval m row).val then yes.eval m row else no.eval m row := by
  simp only [Expr.eval, Comparison.test, decide_eq_true_eq, Fin.lt_def]

private theorem branch_eq (x y yes no : Expr) (m : Memory w) (row : Word w) :
    (Expr.branch .eq x y yes no).eval m row =
      if (x.eval m row).val = (y.eval m row).val then yes.eval m row else no.eval m row := by
  simp only [Expr.eval, Comparison.test, beq_iff_eq, Fin.ext_iff]

theorem indicator_eval (keys : Bank) (m : Memory w) (key : Fin n→ℕ) (hn : n≤keys.size)
    (hw : keys.size<2^w) (loaded : ∀i,(m (keys.base+i.val)).val=key i) (i j : Fin n) :
    (indicator keys j).eval m (i.val:Word w)=if before key j i then 1 else 0 := by
  have ri := lookup keys i m hn hw
  have rj := lookup keys j m hn hw
  have vi := Fin.val_cast_of_lt (i.isLt.trans (hn.trans_lt hw))
  have vj := Fin.val_cast_of_lt (j.isLt.trans (hn.trans_lt hw))
  simp only [indicator, branch_lt, branch_eq]
  simp only [Expr.eval, ri, rj, loaded, vi, vj, before, Fin.lt_def, Nat.cast_one, Nat.cast_zero]
  by_cases lo : key j < key i <;> by_cases eqn : key j = key i <;>
    by_cases idx : j.val < i.val <;> simp_all

theorem rank_eval (keys : Bank) (m : Memory w) (key : Fin n→ℕ) (hn : n≤keys.size)
    (hw : keys.size<2^w) (loaded : ∀i,(m (keys.base+i.val)).val=key i) (i : Fin n) :
    (rankExpr n keys).eval m (i.val:Word w)=((order key i).val:Word w) := by
  rw [rankExpr,DescentGLScoreRAM.sumExpr_eval,order_val]
  simp_rw [indicator_eval keys m key hn hw loaded i]
  simp []

def addr (n dest : ℕ) (keys : Bank) : Expr := .op .add (.lit dest) (rankExpr n keys)

def program (w n scratch dest : ℕ) (keys : Bank) (value : Expr) :=
  ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (addr n dest keys) value

def ticks (n dest : ℕ) (keys : Bank) (value : Expr) := ProtocolRAMGeneratedWrite.work n (addr n dest keys) value

def after (scratch dest : ℕ) (keys : Bank) (value : Expr) (key : Fin n→ℕ) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image scratch (scratch+n) (addr n dest keys) value
    (fun i=>dest+(order key i).val) (fun i=>value.eval m (i.val:Word w)) m

private theorem fit (keys : Bank) (dest scratch : ℕ) (room : keys.Fits w scratch) :
    (addr n dest keys).Fits w scratch := by
  apply And.intro trivial
  apply DescentGLScoreRAM.sumExpr_fits
  intro i
  exact ⟨⟨room,trivial⟩,⟨room,trivial⟩,trivial,⟨⟨room,trivial⟩,⟨room,trivial⟩,⟨trivial,trivial,trivial,trivial⟩,trivial⟩⟩

theorem run (scratch dest : ℕ) (keys : Bank) (value : Expr) (key : Fin n→ℕ) (m : Memory w)
    (hn : n≤keys.size) (room : keys.Fits w scratch) (vf : value.Fits w scratch)
    (apart : scratch+n+n≤dest) (bound : dest+n<2^w) (loaded : ∀i,(m (keys.base+i.val)).val=key i) :
    (program w n scratch dest keys value).Exec m (after scratch dest keys value key m) (ticks n dest keys value) := by
  apply ProtocolRAMGeneratedWrite.run _ _ _ _ _ _ _ (fit keys dest scratch room) vf le_rfl (by omega)
  · intro i
    simp [addr,Expr.eval,RowOp.opcode,BinaryOp.eval,rank_eval keys m key hn room.2.1 loaded]
  · intro i
    rfl
  · intro i
    have := (order key i).isLt
    omega
  · intro i j
    have := i.isLt
    omega
  · intro i j
    have := i.isLt
    omega

theorem publish (scratch dest : ℕ) (keys : Bank) (value : Expr) (key : Fin n→ℕ) (m : Memory w) (i : Fin n) :
    after scratch dest keys value key m (dest+(order key i).val)=value.eval m (i.val:Word w) := by
  apply ProtocolRAMGeneratedWrite.read
  intro i j h
  exact (order key).injective (Fin.ext (Nat.add_left_cancel h))

theorem below (scratch dest : ℕ) (keys : Bank) (value : Expr) (key : Fin n→ℕ) (m : Memory w)
    {x : ℕ} (hx : x<scratch) (sd : scratch≤dest) : after scratch dest keys value key m x=m x :=
  ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ (fun i=>by omega) (.inl hx) (.inl (by omega))

theorem ticks_le (n dest : ℕ) (keys : Bank) (value : Expr) :
    ticks n dest keys value≤11+n*(96*n+2*value.work+32) := by
  have rankWork : (rankExpr n keys).work ≤ 1+n*47 :=
    DescentGLScoreRAM.sumExpr_work (n:=n) (U:=46) (indicator keys) (fun _ => by
      change 36 ≤ 46
      decide)
  have addressWork : (addr n dest keys).work ≤ 1+n*47+2 := by
    change 1+(rankExpr n keys).work+1 ≤ 1+n*47+2
    omega
  unfold ticks ProtocolRAMGeneratedWrite.work
  calc
    _ ≤ (4+n*(2*(1+n*47+2)+4))+(4+n*(2*value.work+4))+(3+10*n) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem cheap (w n scratch dest : ℕ) (keys : Bank) (value : Expr) :
    CheapCode (program w n scratch dest keys value) :=
  ProtocolRAMRankCheap.generated w scratch (scratch+n) n (addr n dest keys) value

end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
