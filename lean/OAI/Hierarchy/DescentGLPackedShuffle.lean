import OAI.Hierarchy.DescentGLPackedRoutes
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # A native, packed, two-word shuffle for one selected binary elementary row operation -/
namespace Hierarchy.DescentGLPacked
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {A I : Type} {P K b H w : ℕ}

abbrev Lane (I : Type) (b : ℕ) := I→Cell b

def packet (lan : I≃Fin K) (x : I→Cell b) : Cell (b*K) := encode b K (fun j=>x (lan.symm j))

def codec (R : Route A I) (lan : I≃Fin K) (f : Bool) (key : Cell ((b+b)*K)) : Cell (b*K) :=
  let z:=(DescentPackedZip.key b b K).symm key
  packet lan (fun j=>((encode b K).symm (if R.select f j then z.2 else z.1)) (lan (R.localAt f j)))

def ordinal (name : A≃Fin P) (h : Fin H) (v : A) : Fin (H*P) := finProdFinEquiv (h,name v)

theorem codec_read (R : Route A I) (lan : I≃Fin K) (x : A→I→Cell b) (v : A) :
    codec R lan (R.family v) (DescentPackedZip.key b b K (packet lan (x (R.left v)),packet lan (x (R.right v))))=
    packet lan (fun j=>let u:=R.pull (v,j);x u.1 u.2) := by
  unfold codec
  rw [Equiv.symm_apply_apply]
  apply congrArg (packet lan)
  funext i
  by_cases p : R.select (R.family v) i <;> simp [p,Route.pull,packet]

structure Board where
  left : Bank
  right : Bank
  variant : Bank
  shift : Bank
  table : Bool→Bank

def part (B : Board) (src : Bank) (which : Bool) : Expr :=
  .lookup src (.lookup (if which then B.right else B.left) .row)

def combined (B : Board) (src : Bank) : Expr := .op .add (part B src true) (.lookup B.shift (part B src false))

def enabled (B : Board) (src : Bank) : Expr :=
  .branch .eq (.lookup B.variant .row) (.lit 0) (.lookup (B.table false) (combined B src))
    (.lookup (B.table true) (combined B src))

def lookup (B : Board) (src ctrl : Bank) : Expr :=
  .branch .eq (.lookup ctrl (.lit 0)) (.lit 0) (.lookup src .row) (enabled B src)

structure Room (B : Board) (source ctrl : Bank) (b K H P w out : ℕ) : Prop where
  src : source.Fits w out
  ctrl : ctrl.Fits w out
  left : B.left.Fits w out
  right : B.right.Fits w out
  variant : B.variant.Fits w out
  shift : B.shift.Fits w out
  table (f : Bool) : (B.table f).Fits w out
  srcSize : H*P ≤ source.size
  leftSize : H*P≤B.left.size
  rightSize : H*P≤B.right.size
  variantSize : H*P≤B.variant.size
  shiftSize : 2^(b*K)≤B.shift.size
  tableSize (f : Bool) : 2^((b+b)*K)≤(B.table f).size
  endFits : out+H*P<2^w

def Reads (src : Bank) (name : A≃Fin P) (lan : I≃Fin K) (x : Fin H→A→I→Cell b) (m : Memory w) : Prop :=
  ∀h v,m (src.base+(ordinal name h v).val)=((packet lan (x h v)).val:Word w)

structure Static (B : Board) (R : Route A I) (name : A≃Fin P) (lan : I≃Fin K) (b H : ℕ) (m : Memory w) : Prop where
  left (h : Fin H) (v : A) : m (B.left.base+(ordinal name h v).val)=((ordinal name h (R.left v)).val:Word w)
  right (h : Fin H) (v : A) : m (B.right.base+(ordinal name h v).val)=((ordinal name h (R.right v)).val:Word w)
  family (h : Fin H) (v : A) : m (B.variant.base+(ordinal name h v).val)=((R.family v).toNat:Word w)
  shift (x : Cell (b*K)) : m (B.shift.base+x.val)=((2^(b*K)*x.val:ℕ):Word w)
  tables (f : Bool) (x : Cell ((b+b)*K)) : m ((B.table f).base+x.val)=((codec R lan f x).val:Word w)

def step (R : Route A I) (go : Bool) (x : Fin H→A→I→Cell b) (h : Fin H) (v : A) (i : I) :=
  if go then let p:=R.pull (v,i);x h p.1 p.2 else x h v i

theorem read (B : Board) (src ctrl : Bank) (out : ℕ) (z : Room B src ctrl b K H P w out)
    (R : Route A I) (name : A≃Fin P) (lan : I≃Fin K) (x : Fin H→A→I→Cell b) (go : Bool)
    (m : Memory w) (mem : Reads src name lan x m) (rom : Static B R name lan b H m)
    (flag : m ctrl.base=(go.toNat:Word w)) (h : Fin H) (v : A) :
    (lookup B src ctrl).eval m ((ordinal name h v).val:Word w)=((packet lan (step R go x h v)).val:Word w) := by
  let u:=ordinal name h v
  let readL:=packet lan (x h (R.left v))
  let readR:=packet lan (x h (R.right v))
  have small:=u.isLt
  have one : (1:Word w)≠0 := by
    have pos : 1<2^w := (Nat.one_le_of_lt z.ctrl.1).trans_lt z.ctrl.2.1
    intro eq;have h:=congrArg Fin.val eq;simp [Nat.mod_eq_of_lt pos] at h
  have flagRead : ctrl.read m (0:Word w)=(go.toNat:Word w) := by simpa [Bank.read] using flag
  have leftRead : (part B src false).eval m (u.val:Word w)=(readL.val:Word w) := by
    have pointer := (DescentPackedZip.bank_read B.left m (small.trans_le z.leftSize) z.left).trans (rom.left h v)
    change src.read m (B.left.read m (u.val:Word w))=_
    rw [pointer]
    exact (DescentPackedZip.bank_read src m ((ordinal name h (R.left v)).isLt.trans_le z.srcSize) z.src).trans (mem h (R.left v))
  have rightRead : (part B src true).eval m (u.val:Word w)=(readR.val:Word w) := by
    have pointer := (DescentPackedZip.bank_read B.right m (small.trans_le z.rightSize) z.right).trans (rom.right h v)
    change src.read m (B.right.read m (u.val:Word w))=_
    rw [pointer]
    exact (DescentPackedZip.bank_read src m ((ordinal name h (R.right v)).isLt.trans_le z.srcSize) z.src).trans (mem h (R.right v))
  let ix:=DescentPackedZip.key b b K (readL,readR)
  have keyRead : (combined B src).eval m (u.val:Word w)=(ix.val:Word w) := by
    have shifted : B.shift.read m (readL.val:Word w)=((2^(b*K)*readL.val:ℕ):Word w) :=
      (DescentPackedZip.bank_read B.shift m (readL.isLt.trans_le z.shiftSize) z.shift).trans (rom.shift readL)
    change (part B src true).eval m (u.val:Word w) +
      B.shift.read m ((part B src false).eval m (u.val:Word w))=(ix.val:Word w)
    rw [rightRead,leftRead,shifted]
    exact (Nat.cast_add readR.val (2^(b*K)*readL.val)).symm
  have got (f : Bool) : ((Expr.lookup (B.table f) (combined B src)).eval m (u.val:Word w))=((codec R lan f ix).val:Word w) := by
    rw [Expr.eval,keyRead,DescentPackedZip.bank_read _ _ (ix.isLt.trans_le (z.tableSize f)) (z.table f),rom.tables]
  change (lookup B src ctrl).eval m (u.val:Word w)=_
  cases go with
  | false=>
    have keep : (lookup B src ctrl).eval m (u.val:Word w)=src.read m (u.val:Word w) := by
      change (if DescriptorExpr.Comparison.eq.test (ctrl.read m 0) (0:Word w)=true then
        src.read m (u.val:Word w) else (enabled B src).eval m (u.val:Word w))=_
      rw [flagRead]; simp [DescriptorExpr.Comparison.test]
    exact keep.trans ((DescentPackedZip.bank_read src m (small.trans_le z.srcSize) z.src).trans (mem h v))
  | true=>
    have gain:=congrArg (fun c : Cell (b*K)=>(c.val:Word w)) (codec_read R lan (x h) v)
    change ((codec R lan (R.family v) ix).val:Word w)=_ at gain
    have mode : (Expr.lookup B.variant .row).eval m (u.val:Word w)=((R.family v).toNat:Word w) := by
      rw [Expr.eval,Expr.eval,DescentPackedZip.bank_read _ _ (small.trans_le z.variantSize) z.variant,rom.family]
    change (lookup B src ctrl).eval m (u.val:Word w)=((packet lan (fun j=>let p:=R.pull (v,j);x h p.1 p.2)).val:Word w)
    have run : (lookup B src ctrl).eval m (u.val:Word w)=(enabled B src).eval m (u.val:Word w) := by
      change (if DescriptorExpr.Comparison.eq.test (ctrl.read m 0) (0:Word w)=true then
        src.read m (u.val:Word w) else (enabled B src).eval m (u.val:Word w))=_
      rw [flagRead]; simp [DescriptorExpr.Comparison.test,one]
    refine run.trans (Eq.trans ?_ gain)
    change (if DescriptorExpr.Comparison.eq.test ((Expr.lookup B.variant .row).eval m (u.val:Word w)) (0:Word w)=true then
      (Expr.lookup (B.table false) (combined B src)).eval m (u.val:Word w)
      else (Expr.lookup (B.table true) (combined B src)).eval m (u.val:Word w))=_
    rw [mode]
    cases R.family v <;> simp [DescriptorExpr.Comparison.test,one,got]

theorem eval_fits (B : Board) (src ctrl : Bank) (out : ℕ) (z : Room B src ctrl b K H P w out) :
    (lookup B src ctrl).Fits w out := by
  simp [lookup,enabled,combined,part,Expr.Fits,z.ctrl,z.variant,z.src,z.left,z.right,z.shift,z.table]

theorem native (B : Board) (src ctrl : Bank) (out : ℕ) (z : Room B src ctrl b K H P w out)
    (R : Route A I) (name : A≃Fin P) (lan : I≃Fin K) (x : Fin H→A→I→Cell b) (go : Bool) :
    (scan w out (H*P) (lookup B src ctrl)).Spec
      (fun m=>Reads src name lan x m ∧ Static B R name lan b H m ∧ m ctrl.base=(go.toNat:Word w))
      (fun old m=> m=image out (H*P) (lookup B src ctrl) old ∧
        ∀ h v,m (out+(ordinal name h v).val)=((packet lan (step R go x h v)).val:Word w))
      (4+(H*P)*(2*(lookup B src ctrl).work+4)) ∧ CheapCode (scan w out (H*P) (lookup B src ctrl)) := by
  refine ⟨?_,scan_cheap w out (H*P) (lookup B src ctrl)⟩
  intro Q N W mach pc reg pub exit rom regs cfg m start pre
  obtain ⟨time,ticks,done,after,ran,ended,mem⟩:=scan_exec out (H*P) (lookup B src ctrl) m
    (eval_fits B src ctrl out z) z.endFits mach pc reg pub exit rom regs cfg m start rfl
  refine ⟨time,ticks,done,after,ran,ended,mem,?_⟩
  intro h v
  have small:=(ordinal name h v).isLt
  rw [mem]
  simpa [image,fillSegment,show out≤out+(ordinal name h v).val ∧ out+(ordinal name h v).val<out+H*P by omega] using
    read B src ctrl out z R name lan x go m pre.1 pre.2.1 pre.2.2 h v

theorem work (B : Board) (src ctrl : Bank) : (lookup B src ctrl).work≤110 := by
  change 94 ≤ 110
  decide

theorem table_cost (b K dataWidth : ℕ) (room : (b+b)*K≤dataWidth/2) :
    2^(b*K)+2*2^((b+b)*K)≤3*2^(dataWidth/2) := by
  have bigger : b*K≤(b+b)*K:=Nat.mul_le_mul_right K (Nat.le_add_right ..)
  have wide:=Nat.pow_le_pow_right (by decide : 0<2) room
  have small:=Nat.pow_le_pow_right (by decide : 0<2) (bigger.trans room)
  omega

end
end Hierarchy.DescentGLPacked

end OAI
