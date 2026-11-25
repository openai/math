import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordColumn
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # One lookup from the actual terminal operand and signed-cable pages at each common host -/
namespace Hierarchy.DescentTerminalPointerFrame
open DescentSIMDLookup ProtocolRAM ProtocolRAMGeneratedWrite Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {L d b H w : ℕ}

def weighted (xs : Fin L→ Cell d) (j : Fin L) := (xs j).val*(2^d)^j.val

def offset (base d : ℕ) (j : Fin L) : Bank := ⟨base+j.val*2^d,d⟩
def dictionary (L d base : ℕ) : Bank := ⟨base+L*2^d,d*L⟩
def size (L d : ℕ) := L*2^d+2^(d*L)

def literal (f : (Fin L→ Cell d)→ Cell b) (i : ℕ) : ℕ :=
  if i < L*2^d then i%2^d*(2^d)^(i/2^d)
  else (f ((encode d L).symm ((i-L*2^d:ℕ):Cell (d*L)))).val

def terms (base d : ℕ) (src : Fin L→ Bank) (j : Fin L) : Expr := .lookup (offset base d j) (.lookup (src j) .row)
def add (f : Fin L→ Expr) : List (Fin L)→ Expr
  | []=>.lit 0
  | i::xs=>.op .add (f i) (add f xs)
def row (base d : ℕ) (src : Fin L→ Bank) : Expr := .lookup (dictionary L d base) (add (terms base d src) (List.finRange L))
def mount (base w : ℕ) (f : (Fin L→ Cell d)→ Cell b) := DescentStaticWordColumn.program w base (literal f) (size L d)
def mounted (base : ℕ) (f : (Fin L→ Cell d)→ Cell b) (m : Memory w) := DescentStaticWordColumn.image base (literal f) m (size L d)
def program (w base : ℕ) (src : Fin L→ Bank) (H : ℕ) (f : (Fin L→ Cell d)→ Cell b) :=
  (mount base w f).seq (scan w (base+size L d) H (row base d src))
def result (base : ℕ) (src : Fin L→ Bank) (H : ℕ) (f : (Fin L→ Cell d)→ Cell b) (m : Memory w) :=
  image (base+size L d) H (row base d src) (mounted base f m)

private theorem add_read (fs : Fin L→ Expr) (m : Memory w) (j : Word w) (z : Fin L→ℕ)
    (actual : ∀i,(fs i).eval m j=(z i:Word w)) (xs : List (Fin L)) :
    (add fs xs).eval m j=((xs.map z).sum:Word w) := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>simp [add,Expr.eval,RowOp.opcode,BinaryOp.eval,actual,ih,Nat.cast_add]

private theorem add_fits (fs : Fin L→ Expr) (out₀ : ℕ) (ready : ∀i,(fs i).Fits w out₀) (xs : List (Fin L)) :
    (add fs xs).Fits w out₀ := by induction xs with | nil=>trivial | cons i xs ih=>exact ⟨ready i,ih⟩

private theorem adder_work (fs : Fin L→ Expr) (len : ∀i,(fs i).work=12) (xs : List (Fin L)) :
    (add fs xs).work=1+13*xs.length := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>simp [add,Expr.work,len,ih];omega

theorem row_work (src : Fin L→ Bank) (base d : ℕ) : (row base d src).work=6+13*L := by
  change (add (terms base d src) (List.finRange L)).work+5=_
  rw [adder_work _ (fun j=>rfl),List.length_finRange];omega

structure Room (src : Fin L→ Bank) (base d H w : ℕ) : Prop where
  source : ∀j,(src j).Fits w base
  length : ∀j,H≤(src j).size
  offsets : 2^d < 2^w
  limit : base+size L d+H < 2^w

private theorem fits (base : ℕ) (src : Fin L→ Bank) (ok : Room src base d H w) :
    (row base d src).Fits w (base+size L d) := by
  have endAt:=ok.limit
  unfold size at *
  refine ⟨⟨Nat.two_pow_pos _,by change 2^(d*L) < 2^w;omega,by change (base+L*2^d)+2^(d*L)≤_;omega⟩,?_⟩
  apply add_fits
  intro j
  have inside:=Nat.mul_le_mul_right (2^d) j.isLt
  rw [Nat.succ_mul] at inside
  exact ⟨⟨Nat.two_pow_pos _,ok.offsets,by change base+j.val*2^d+2^d≤base+(L*2^d+2^(d*L));rw [Nat.add_assoc];exact Nat.add_le_add_left (inside.trans (Nat.le_add_right _ _)) _⟩,
    ⟨(ok.source j).1,(ok.source j).2.1,(ok.source j).2.2.trans (Nat.le_add_right ..)⟩,trivial⟩

private theorem cheap_mount (w addr n : ℕ) (f : ℕ→ℕ) : CheapCode (DescentStaticWordColumn.program w addr f n) := by
  induction n with
  | zero=>exact scan_cheap w addr 0 (.lit 0)
  | succ n ih=>exact cheap_seq ih (scan_cheap w (addr+n) 1 (.lit (f n)))

theorem run (base : ℕ) (src : Fin L→ Bank) (f : (Fin L→ Cell d)→ Cell b) (m : Memory w) (ok : Room src base d H w) :
    (program w base src H f).Exec m (result base src H f m) ((4+10*size L d)+(4+H*(16+26*L))) ∧
    CheapCode (program w base src H f) ∧
    ∀j,j < base ∨ base+size L d+H≤j→ result base src H f m j=m j := by
  have load : (mount base w f).Exec m (mounted base f m) (4+10*size L d):=DescentStaticWordColumn.mount base (size L d) (literal f) m (by have:=ok.limit;omega)
  have issue : (scan w (base+size L d) H (row base d src)).Exec (mounted base f m) (result base src H f m)
      (4+H*(2*(row base d src).work+4)):=scan_exec (base+size L d) H (row base d src) (mounted base f m) (fits base src ok) ok.limit
  refine ⟨?_,cheap_seq (cheap_mount w base (size L d) (literal f)) (scan_cheap w (base+size L d) H (row base d src)),?_⟩
  · rw [←show 2*(row base d src).work+4=16+26*L by rw [row_work];omega]
    intro P R K run
    exact Procedure.Exec.then load issue run
  · intro j away
    exact (frame_image _ _ _ _ _ (by omega)).trans (DescentStaticWordColumn.frame _ _ _ _ _ (by omega))

theorem read_masked (base : ℕ) (src : Fin L→ Bank) (f : (Fin L→ Cell d)→ Cell b) (m : Memory w) (ok : Room src base d H w)
    (x : Fin H→ Fin L→ Cell d) (physical : ∀i j,(m ((src j).base+i.val)).val%2^d=(x i j).val) (i : Fin H) :
    result base src H f m (base+size L d+i.val)=((f (x i)).val:Word w) := by
  let warm:=mounted base f m
  have stop:=ok.limit
  have last:2^(d*L) < 2^w:=by unfold size at stop;omega
  have digit (j : Fin L) : (terms base d src j).eval warm (i.val:Word w)=(weighted (x i) j:Word w) := by
    have a:=i.isLt.trans_le (ok.length j)
    have below:= (ok.source j).2.2
    have inp:=(DescentPackedZip.bank_read (src j) warm a (ok.source j)).trans
      (DescentStaticWordColumn.frame base (size L d) _ m _ (.inl (by omega)))
    change (offset base d j).read warm ((src j).read warm (i.val:Word w))=_
    rw [inp]
    have z:=(x i j).isLt
    have idx:=Nat.mul_le_mul_right (2^d) j.isLt
    rw [Nat.succ_mul] at idx
    have good : j.val*2^d+(x i j).val < L*2^d:=by omega
    change warm (base+j.val*2^d+(m ((src j).base+i.val)).val%2^d)=_
    rw [physical i j]
    dsimp only [warm,mounted]
    rw [Nat.add_assoc,DescentStaticWordColumn.read base (size L d) (literal f) m (good.trans_le (Nat.le_add_right ..))]
    have quotient : (j.val*2^d+(x i j).val)/2^d=j.val := by
      rw [Nat.mul_comm j.val,Nat.mul_add_div (Nat.two_pow_pos d),Nat.div_eq_of_lt z,Nat.add_zero]
    have rem_ : (j.val*2^d+(x i j).val)%2^d=(x i j).val := by
      rw [Nat.mul_comm j.val,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt z]
    simp only [literal,ite_eq_left good,quotient,rem_,weighted]
  have total:((List.finRange L).map (weighted (x i))).sum=(encode d L (x i)).val := by
    rw [show (encode d L (x i)).val=(finFunctionFinEquiv (x i)).val from rfl,finFunctionFinEquiv_apply]
    rw [←List.ofFn_eq_map]
    simp [List.sum_ofFn,weighted]
  rw [result,read_image]
  change (dictionary L d base).read warm ((add (terms base d src) _).eval warm (i.val:Word w))=_
  rw [add_read _ _ _ _ digit,total]
  let j:=encode d L (x i)
  have rf : (dictionary L d base).Fits w (base+size L d):=⟨Nat.two_pow_pos _,last,by change base+L*2^d+2^(d*L)≤base+(L*2^d+2^(d*L));omega⟩
  rw [DescentPackedZip.bank_read _ _ j.isLt rf]
  change warm (base+L*2^d+j.val)=_
  have within:=j.isLt
  dsimp only [warm,mounted]
  rw [Nat.add_assoc,DescentStaticWordColumn.read base (size L d) (literal f) m (show L*2^d+j.val < size L d by unfold size;omega)]
  simp [literal,j,Equiv.symm_apply_apply]

theorem read (base : ℕ) (src : Fin L→ Bank) (f : (Fin L→ Cell d)→ Cell b) (m : Memory w) (ok : Room src base d H w)
    (x : Fin H→ Fin L→ Cell d) (physical : ∀i j,m ((src j).base+i.val)=((x i j).val:Word w)) (i : Fin H) :
    result base src H f m (base+size L d+i.val)=((f (x i)).val:Word w) := by
  apply read_masked base src f m ok x _ i
  intro h j
  rw [physical,Fin.val_cast_of_lt ((x h j).isLt.trans ok.offsets),Nat.mod_eq_of_lt (x h j).isLt]

end
end Hierarchy.DescentTerminalPointerFrame

end OAI
