import OAI.Hierarchy.DescentExteriorMatrixUpdate
import OAI.Hierarchy.DescentGLPermutationRAM

namespace OAI
/-! # Reading the selected physical GL rows into a unique matrix ordinal -/
namespace Hierarchy.DescentExteriorSelectedMatrix
open DescentGL DescentExterior ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

def number (k : ℕ) : (d : ℕ)→(Fin d→Word k)→Fin ((2^k)^d)
  | 0,_=>⟨0,by simp⟩
  | d+1,f=>Fin.cast (pow_succ ..).symm
    (finProdFinEquiv (number k d (fun i=>f i.succ),f 0))

theorem number_injective (k : ℕ) (d : ℕ) : Function.Injective (number k d) := by
  induction d with
  | zero=>intro x y _;funext i;exact i.elim0
  | succ d ih=>
    intro f g h
    have pair : (number k d (fun i=>f i.succ),f 0)=(number k d (fun i=>g i.succ),g 0) := by
      apply finProdFinEquiv.injective
      apply Fin.ext
      exact congrArg Fin.val h
    have tail:=ih (congrArg Prod.fst pair)
    funext i
    exact Fin.cases (congrArg Prod.snd pair) (fun j=>congrFun tail j) i

def ord {k : ℕ} (L : Layout k) := number k k (fun a=>rowIndex k (rowFunctional L a))

theorem ord_injective (k : ℕ) : Function.Injective (ord (k:=k)) := by
  intro f g h
  have all:=number_injective k k h
  ext x i
  simpa only [rowFunctional_apply] using
    congrArg (fun t : Row k=>t x) ((rowIndex k).injective (congrFun all i))

/-- Distinct codings of bit rows and bit matrices agree via a single
immutable lookup. Every valid key refers to the actual chosen layout. -/
def decode (k : ℕ) : Fin ((2^k)^k)→Word (k*k) := Function.extend ord matrixCode (fun _=>0)

@[simp] theorem decode_ord {k : ℕ} (M : Layout k) : decode k (ord M)=matrixCode M :=
  (ord_injective k).extend_apply _ _ _

def expr (offset : Bank) : (d : ℕ)→(Fin d→ℕ)→Expr
  | 0,_=>.lit 0
  | d+1,ptr=>.op .add (.lookup ⟨ptr 0,0⟩ (.lit 0))
      (.lookup offset (expr offset d (fun i=>ptr i.succ)))

theorem expr_work (offset : Bank) (d : ℕ) (ptr : Fin d→ℕ) : (expr offset d ptr).work=1+12*d := by
  induction d with
  | zero=>rfl
  | succ d ih=>simp [expr,Expr.work,ih,Nat.mul_succ];omega

theorem expr_fits {w out : ℕ} (offset : Bank) (ok : offset.Fits w out)
    (wide : 1<2^w) (d : ℕ) (ptr : Fin d→ℕ) (above : ∀i,ptr i<out) : (expr offset d ptr).Fits w out := by
  induction d with
  | zero=>trivial
  | succ d ih=>
    exact ⟨⟨⟨show 0 < 2^0 by decide,wide,Nat.succ_le_of_lt (above 0)⟩,trivial⟩,
      ok,ih _ (fun i=>above i.succ)⟩

private theorem lookup_at {w out : ℕ} (b : Bank) (m : Memory w) (x : ℕ) (fit : b.Fits w out)
    (small : x<b.size) : b.read m (x:Word w)=m (b.base+x) := by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

theorem expr_read {w out k : ℕ} (offset : Bank) (ok : offset.Fits w out)
    (space : (2^k)^k≤offset.size) (m : Memory w)
    (offsets : ∀i:Fin ((2^k)^k),m (offset.base+i.val)=((2^k*i.val:ℕ):Word w))
    (d : ℕ) (small : d≤k) (ptr : Fin d→ℕ) (val : Fin d→Word k)
    (store : ∀i,m (ptr i)=(val i).val) (row : Word w) :
    (expr offset d ptr).eval m row=((number k d val).val:Word w) := by
  induction d with
  | zero=>rfl
  | succ d ih=>
    let tail:=number k d (fun i=>val i.succ)
    have before : (2^k)^d≤(2^k)^k:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)
    let ix : Fin ((2^k)^k):=⟨tail.val,tail.isLt.trans_le before⟩
    have atHead : (⟨ptr 0,0⟩:Bank).read m ((0:ℕ):Word w)=m (ptr 0) := by simp [Bank.read]
    simp only [expr,Expr.eval,RowOp.opcode,BinaryOp.eval]
    rw [atHead,store (0 : Fin (d+1))]
    rw [ih (by omega) _ _ (fun j=>store j.succ),lookup_at offset m _ ok (ix.isLt.trans_le space),offsets ix]
    change ((val 0).val:Word w)+((2^k*tail.val:ℕ):Word w)=(((val 0).val+2^k*tail.val:ℕ):Word w)
    simp

theorem program_read {w out k : ℕ} (offset table : Bank) (ofit : offset.Fits w out)
    (tfit : table.Fits w out) (os : (2^k)^k≤offset.size) (ts : (2^k)^k≤table.size)
    (m : Memory w) (offsets : ∀i:Fin ((2^k)^k),m (offset.base+i.val)=((2^k*i.val:ℕ):Word w))
    (words : ∀i:Fin ((2^k)^k),m (table.base+i.val)=((decode k i).val:Word w))
    (ptr : Fin k→ℕ) (M : Layout k) (selected : DescentGLPermutationRAM.stored ptr m M) (row : Word w) :
    (.lookup table (expr offset k ptr) : Expr).eval m row=((matrixCode M).val:Word w) := by
  simp only [Expr.eval]
  rw [expr_read offset ofit os m offsets k le_rfl ptr (fun i=>rowIndex k (rowFunctional M i)) selected]
  change table.read m ((ord M).val : Word w) = ((matrixCode M).val : Word w)
  rw [lookup_at table m _ tfit ((ord M).isLt.trans_le ts),words (ord M),decode_ord]

/-- The copy from the selector's actual published row cells takes a single
output scan. The only growing term in the instruction and step bill is the
number of selected rows, even though the advice is shared across visits. -/
theorem run {w out k : ℕ} (offset table : Bank) (ofit : offset.Fits w out)
    (tfit : table.Fits w out) (os : (2^k)^k≤offset.size) (ts : (2^k)^k≤table.size)
    (fit : out+1<2^w) (ptr : Fin k→ℕ) (below : ∀i,ptr i<out) (M : Layout k) :
    let op:=Expr.lookup table (expr offset k ptr)
    (scan w out 1 op).Spec (fun m=>
      (∀i:Fin ((2^k)^k),m (offset.base+i.val)=((2^k*i.val:ℕ):Word w)) ∧
      (∀i:Fin ((2^k)^k),m (table.base+i.val)=((decode k i).val:Word w)) ∧
      DescentGLPermutationRAM.stored ptr m M)
      (fun m dst=>dst=image out 1 op m ∧ dst out=((matrixCode M).val:Word w)) (20+24*k) ∧
      CheapCode (scan w out 1 op) := by
  intro op
  have ok : op.Fits w out:=⟨tfit,expr_fits offset ofit (by omega) k ptr below⟩
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  intro P X A machine pc reg pub exit rom «public» cfg m start data
  obtain ⟨cnt,cost,done,after,adv,stop,eq⟩:=scan_exec out 1 op m ok fit
    machine pc reg pub exit rom «public» cfg m start rfl
  refine ⟨cnt,?_,done,after,adv,stop,eq,?_⟩
  · have wk : op.work=1+12*k+5:=by simp [op,Expr.work,expr_work]
    rw [wk] at cost
    omega
  · rw [eq]
    simpa [ProtocolRAM.image,fillSegment,op] using
      program_read offset table ofit tfit os ts m data.1 data.2.1 ptr M data.2.2 (0:Word w)

theorem advice_words (k w : ℕ) (fit : k*k≤w/2) : 2*((2^k)^k)≤2*2^(w/2) := by
  rw [←pow_mul]
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) fit)

end
end Hierarchy.DescentExteriorSelectedMatrix

end OAI
