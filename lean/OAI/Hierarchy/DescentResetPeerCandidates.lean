import OAI.Hierarchy.DescentResetPeerPackedFlags

namespace OAI
/-! # Lift the measured old host ports into the new sparse shape rectangle -/
namespace Hierarchy.DescentResetPeerUnionRAM.Candidates
open DescentSIMDLookup DescentPackedColony DescentIssuedTerminalId ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H S D w : ℕ}

def count (shapes degree : ℕ) := (degree+1)*shapes+3
def candidate (old : Fin H→Fin D→Option (Fin H)) (v : Fin (H*S)) (j : Fin (count S D)) : Option (Fin (H*S)) :=
  if h : j.val < (D+1)*S then
    let key:=finProdFinEquiv.symm (⟨j.val,h⟩ : Fin ((D+1)*S))
    let parent:=(finProdFinEquiv.symm v).1
    let next:=if small : key.1.val < D then old parent ⟨_,small⟩ else some parent
    next.map fun host=>finProdFinEquiv (host,key.2)
  else none

def atSlot (slot : Fin (D+1)) (shape : Fin S) : Fin (count S D) :=
  (finProdFinEquiv (slot,shape)).castLE (Nat.le_add_right _ 3)

theorem atSlot_val (socket : Fin (D+1)) (other : Fin S) :
    (atSlot socket other).val=socket.val*S+other.val := by
  change other.val + S * socket.val = socket.val * S + other.val
  ac_rfl

private theorem candidate_atSlot (old : Fin H → Fin D → Option (Fin H)) (v : Fin H)
    (here other : Fin S) (a : Fin (D+1)) :
    candidate old (finProdFinEquiv (v,here)) (atSlot a other) =
      (if h : a.val < D then old v ⟨a.val,h⟩ else some v).map (fun u => finProdFinEquiv (u,other)) := by
  have valid : (atSlot a other).val < (D+1)*S := (finProdFinEquiv (a,other)).isLt
  have key : (⟨(atSlot a other).val,valid⟩ : Fin ((D+1)*S)) = finProdFinEquiv (a,other) := rfl
  simp only [candidate,dite_eq_left valid,key,Equiv.symm_apply_apply]

theorem specific (old : Fin H→Fin D→Option (Fin H)) (v : Fin H) (here : Fin S)
    (socket : Fin D) (other : Fin S) :
    candidate old (finProdFinEquiv (v,here)) (atSlot socket.castSucc other)=
      (old v socket).map (fun u=>finProdFinEquiv (u,other)) := by
  rw [candidate_atSlot]
  simp only [Fin.val_castSucc,dite_eq_left socket.isLt]

theorem selfKey (old : Fin H→Fin D→Option (Fin H)) (v : Fin H) (here other : Fin S) :
    candidate old (finProdFinEquiv (v,here)) (atSlot (Fin.last D) other)=some (finProdFinEquiv (v,other)) := by
  rw [candidate_atSlot, dite_eq_right (show ¬(Fin.last D).val < D from Nat.lt_irrefl D),
    Option.map_some]

theorem cover (old : Fin H→Fin D→Option (Fin H)) (v u : Fin H) (x y : Fin S)
    (reach : v=u ∨ ∃j,old v j=some u) :
    ∃t,candidate old (finProdFinEquiv (v,x)) t=some (finProdFinEquiv (u,y)) := by
  rcases reach with h | ⟨j,jr⟩
  · subst u
    exact ⟨atSlot (Fin.last D) y,selfKey old v x y⟩
  · refine ⟨atSlot j.castSucc y,?_⟩
    simp only [specific,jr,Option.map_some]

def current (base H S : ℕ) : Bank := ⟨base,pageBits (H*S)⟩
def starts (base H S : ℕ) : Bank := ⟨base+stride (H*S),pageBits (H*S)⟩
def offsets (base H S : ℕ) : Bank := ⟨base+2*stride (H*S),pageBits H⟩
def length (H S : ℕ) := 2*stride (H*S)+stride H
def literal (H S D i : ℕ) :=
  if i < stride (H*S) then i/S else if i < 2*stride (H*S) then (i-stride (H*S))/S*D
  else (i-2*stride (H*S))*S

def selector (old : Bank) (base H S D : ℕ) (j : Fin (count S D)) : Expr :=
  if h : j.val < (D+1)*S then
    let key:=finProdFinEquiv.symm (⟨j.val,h⟩ : Fin ((D+1)*S))
    let host:=if key.1.val < D then
      Expr.lookup old (.op .add (.lookup (starts base H S) .row) (.lit key.1.val))
      else .lookup (current base H S) .row
    .branch .lt host (.lit H) (.op .add (.lookup (offsets base H S) host) (.lit key.2.val)) (.lit (H*S))
  else .lit (H*S)

structure Setup (old : Bank) (base H S D w : ℕ) : Prop where
  oldFit : old.Fits w base
  oldRows : H*D ≤ old.size
  endRoom : base+length H S < 2^w

def printed (base H S D : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (literal H S D) m (length H S)

theorem install (old : Bank) {base : ℕ} (safe : Setup old base H S D w) (m : Memory w) :
    (DescentStaticWordColumn.program w base (literal H S D) (length H S)).Exec m (printed base H S D m) (4+10*length H S) ∧
    ∀a,a < base ∨ base+length H S ≤ a → printed base H S D m a=m a :=
  ⟨DescentStaticWordColumn.mount _ _ _ _ safe.endRoom,fun _a h=>DescentStaticWordColumn.frame _ _ _ _ _ h⟩

private theorem own_row (v : Fin (H*S)) : v.val/S=(finProdFinEquiv.symm v).1.val := rfl

theorem stored (old : Bank) {base : ℕ} (_safe : Setup old base H S D w) (m : Memory w) :
    let out:=printed base H S D m
    (∀v : Fin (H*S),out ((current base H S).base+v.val)=((finProdFinEquiv.symm v).1.val:Word w)) ∧
    (∀v : Fin (H*S),out ((starts base H S).base+v.val)=(((finProdFinEquiv.symm v).1.val*D:ℕ):Word w)) ∧
    (∀v : Fin H,out ((offsets base H S).base+v.val)=((v.val*S:ℕ):Word w)) := by
  dsimp only
  have enough (n : ℕ) : n ≤ stride n := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  constructor
  · intro v
    have j:=v.isLt.trans_le (enough _)
    rw [printed,current,DescentStaticWordColumn.read _ _ _ _ (j:=v.val) (by dsimp [length];omega)]
    rw [literal,ite_eq_left j,own_row]
  constructor
  · intro v
    have j:=v.isLt.trans_le (enough _)
    have range : stride (H*S)+v.val < 2*stride (H*S) := by omega
    change printed base H S D m (base+stride (H*S)+v.val)=_
    rw [Nat.add_assoc,printed,DescentStaticWordColumn.read _ _ _ _ (by dsimp [length];omega)]
    rw [literal,ite_eq_right (by omega : ¬stride (H*S)+v.val < stride (H*S)),ite_eq_left range,
      Nat.add_sub_cancel_left,own_row]
  · intro v
    have j:=v.isLt.trans_le (enough _)
    change printed base H S D m (base+2*stride (H*S)+v.val)=_
    rw [Nat.add_assoc,printed,DescentStaticWordColumn.read _ _ _ _ (by dsimp [length];omega)]
    simp [literal,show ¬2*stride (H*S)+v.val < stride (H*S) by omega]

theorem selected (old : Bank) {base : ℕ} (safe : Setup old base H S D w) (m : Memory w)
    (peers : Fin H→Fin D→Option (Fin H)) (reads : ∀v j,m (old.base+(v.val*D+j.val))=(target (peers v j):Word w))
    (v : Fin (H*S)) (j : Fin (count S D)) :
    (selector old base H S D j).eval (printed base H S D m) (v.val:Word w)=(target (candidate peers v j):Word w) := by
  let out:=printed base H S D m
  obtain ⟨self,first,last⟩:=stored old safe m
  have enough (n : ℕ) : n ≤ stride n := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have end_:=safe.endRoom
  have small : stride (H*S) < 2^w ∧ stride H < 2^w := by dsimp only [length] at end_;omega
  have dims : H < 2^w ∧ H*S < 2^w:=⟨(enough _).trans_lt small.2,(enough _).trans_lt small.1⟩
  by_cases valid : j.val < (D+1)*S
  · let key:=finProdFinEquiv.symm (⟨j.val,valid⟩ : Fin ((D+1)*S))
    let root:=(finProdFinEquiv.symm v).1
    let oldAt:=Expr.lookup old (.op .add (.lookup (starts base H S) .row) (.lit key.1.val))
    let host:=if key.1.val < D then oldAt else .lookup (current base H S) .row
    let next:=if h : key.1.val < D then peers root ⟨_,h⟩ else some root
    have hostRow:host.eval out (v.val:Word w)=(target next:Word w) := by
      by_cases short : key.1.val < D
      · have raw:= (lookup_nat (starts base H S) out (v.val:Word w) .row v.val rfl (v.isLt.trans_le (enough _)) small.1).trans (first v)
        have addr : (Expr.op .add (.lookup (starts base H S) .row) (.lit key.1.val)).eval out (v.val:Word w)=
            ((root.val*D+key.1.val:ℕ):Word w) := by
          change (Expr.lookup _ .row).eval out _+(key.1.val:Word w)=_
          rw [raw,Nat.cast_add]
        have total : root.val*D+key.1.val < H*D :=
          (Nat.add_lt_add_left short _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ root.isLt)
        have prior:= (install old safe m).2 (old.base+(root.val*D+key.1.val)) (.inl (by
          have h:=safe.oldFit.2.2
          have t:=total.trans_le safe.oldRows
          omega))
        simpa only [host,next,ite_eq_left short,dite_eq_left short] using
          (lookup_nat old out _ _ _ addr (total.trans_le safe.oldRows) safe.oldFit.2.1).trans
            (prior.trans (reads root ⟨_,short⟩))
      · simpa only [host,next,ite_eq_right short,dite_eq_right short,target,Option.elim] using
          (lookup_nat (current base H S) out (v.val:Word w) .row v.val rfl
            (v.isLt.trans_le (enough _)) small.1).trans (self v)
    unfold selector candidate
    simp only [dite_eq_left valid]
    change (Expr.branch .lt host (.lit H) (.op .add (.lookup (offsets base H S) host) (.lit key.2.val)) (.lit (H*S))).eval out _=
      (target (next.map fun u=>finProdFinEquiv (u,key.2)):Word w)
    cases ne:next with
    | none=>
      simp [Expr.eval,Comparison.test,hostRow,ne,target]
    | some parent=>
      have ptr : host.eval out (v.val:Word w)=(parent.val:Word w) := by simpa [ne,target] using hostRow
      have low : (parent.val:Word w) < (H:Word w) := by
        rw [Fin.lt_def,Fin.val_cast_of_lt (parent.isLt.trans dims.1),Fin.val_cast_of_lt dims.1]
        exact parent.isLt
      have value:=(lookup_nat (offsets base H S) out (v.val:Word w) host parent.val ptr
        (parent.isLt.trans_le (enough _)) small.2).trans (last parent)
      simp only [Expr.eval,Comparison.test,ptr,decide_eq_true_eq,ite_eq_left low,Option.map_some,target,Option.elim,finProdFinEquiv_apply_val]
      change (offsets base H S).read out (parent.val:Word w)+(key.2.val:Word w)=_
      change (offsets base H S).read out (host.eval out (v.val:Word w))=_ at value
      rw [ptr] at value
      simp only [value,Nat.cast_add,Nat.cast_mul]
      ring
  · simp only [selector,candidate,dite_eq_right valid,Expr.eval,target,Option.elim]

end
end Hierarchy.DescentResetPeerUnionRAM.Candidates

end OAI
