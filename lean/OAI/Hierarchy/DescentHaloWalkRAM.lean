import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Four-hop paths in the native shared rack adjacency -/
namespace Hierarchy.DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H D w : ℕ}
abbrev Path (D : ℕ) := Fin 4→Fin (D+1)
def breadth (D : ℕ) := (D+1)^4
def path (p : Fin (breadth D)) : Path D:=finFunctionFinEquiv.symm p
def row (v : Fin H) (p : Fin (breadth D)) : Fin (H*breadth D):=finProdFinEquiv (v,p)

def number (u : Option (Fin H)) := u.elim H Fin.val

def step (near : Fin H→Fin D→Option (Fin H)) (u : Option (Fin H)) (j : Fin (D+1)) : Option (Fin H) :=
  if live : j.val<D then u.bind (fun v=>near v ⟨j.val,live⟩) else u

def walk (near : Fin H→Fin D→Option (Fin H)) (v : Fin H) (p : Path D) : ℕ→Option (Fin H)
  | 0=>some v
  | t+1=>if inside : t<4 then step near (walk near v p t) (p ⟨t,inside⟩) else walk near v p t

structure Banks where
  adjacency : Bank
  root : Bank
  choice : Fin 4→Bank

structure Fits (B : Banks) (out H D w : ℕ) : Prop where
  adjacency : B.adjacency.Fits w out
  root : B.root.Fits w out
  choice : ∀j,(B.choice j).Fits w out
  adjacencySize : H*D≤B.adjacency.size
  rootSize : H*breadth D≤B.root.size
  choiceSize : ∀j,H*breadth D≤(B.choice j).size
  outside : out+H*breadth D<2^w
  sentinel : H<2^w
  degree : D<2^w

structure Reads (B : Banks) (near : Fin H→Fin D→Option (Fin H)) (m : Memory w) : Prop where
  adjacency : ∀v j,m (B.adjacency.base+v.val*D+j.val)=(number (near v j) : Word w)
  root : ∀(v:Fin H)(p:Fin (breadth D)),m (B.root.base+(row v p).val)=(v.val : Word w)
  choice : ∀(v:Fin H)(p:Fin (breadth D))(j:Fin 4),m ((B.choice j).base+(row v p).val)=((path p j).val : Word w)

def times (f : Expr) : ℕ→Expr
  | 0=>.lit 0
  | n+1=>.op .add (times f n) f

theorem times_at (f : Expr) (m : Memory w) (r : Word w) (n : ℕ) : (times f n).eval m r=(n:Word w)*f.eval m r :=by
  induction n with
  | zero=>simp [times,Expr.eval]
  | succ n ih=>simp [times,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,Nat.cast_add,add_mul]

theorem times_fits {f : Expr} {out} (ok : f.Fits w out) (n : ℕ) : (times f n).Fits w out :=by
  induction n with | zero=>trivial | succ n ih=>exact ⟨ih,ok⟩

theorem times_work (f : Expr) (n : ℕ) : (times f n).work=1+n*(f.work+1) :=by
  induction n with | zero=>simp [times,Expr.work] | succ n ih=>simp [times,Expr.work,ih,Nat.succ_mul];omega

def advance (B : Banks) (H D : ℕ) (u j : Expr) : Expr :=
  .branch .eq j (.lit D) u (.branch .eq u (.lit H) (.lit H) (.lookup B.adjacency (.op .add (times u D) j)))

def body (B : Banks) (H D : ℕ) : ℕ→Expr
  | 0=>.lookup B.root .row
  | t+1=>if inside : t<4 then advance B H D (body B H D t) (.lookup (B.choice ⟨t,inside⟩) .row) else body B H D t

private theorem read_bank (b : Bank) {out i : ℕ} (ok : b.Fits w out) (hi : i<b.size) (m : Memory w) :
    b.read m (i:Word w)=m (b.base+i) :=by simp [Bank.read,Fin.val_cast_of_lt (hi.trans ok.2.1),Nat.mod_eq_of_lt hi]

theorem body_at (B : Banks) (out : ℕ) (room : Fits B out H D w) (near : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (data : Reads B near m) (v : Fin H) (p : Fin (breadth D)) (t : ℕ) :
    (body B H D t).eval m ((row v p).val : Word w)=(number (walk near v (path p) t):Word w) :=by
  let r:=row v p
  induction t with
  | zero=>exact (read_bank B.root room.root (r.isLt.trans_le room.rootSize) m).trans (data.root v p)
  | succ t ih=>
    by_cases active : t<4
    · let a : Fin 4:=⟨t,active⟩;let j:=path p a
      have choice : (B.choice a).read m (r.val:Word w)=(j.val:Word w):=
        (read_bank (B.choice a) (room.choice a) (r.isLt.trans_le (room.choiceSize a)) m).trans (data.choice v p a)
      let u:=walk near v (path p) t
      have old : (body B H D t).eval m (r.val:Word w)=(number u:Word w):=ih
      simp only [body,walk,dite_eq_left active]
      change (advance B H D (body B H D t) (.lookup (B.choice a) .row)).eval m (r.val:Word w)=(number (step near u j):Word w)
      by_cases live : j.val<D
      · have castDiff : (j.val:Word w)≠(D:Word w):=by
          intro eqn;have:=congrArg Fin.val eqn;rw [Fin.val_cast_of_lt (live.trans room.degree),Fin.val_cast_of_lt room.degree] at this;omega
        cases ueq : u with
        | none=>simp [advance,Expr.eval,DescriptorExpr.Comparison.test,choice,old,ueq,number,step,live,castDiff]
        | some h=>
          have destDiff : (h.val:Word w)≠(H:Word w):=by
            intro eqn;have:=congrArg Fin.val eqn;rw [Fin.val_cast_of_lt (h.isLt.trans room.sentinel),Fin.val_cast_of_lt room.sentinel] at this;exact h.isLt.ne this
          have small : h.val*D+j.val<B.adjacency.size:=by
            have top:=Nat.mul_le_mul_right D (Nat.succ_le_of_lt h.isLt);rw [Nat.succ_mul] at top;exact lt_of_lt_of_le (by omega) room.adjacencySize
          have ptr : (D:Word w)*(h.val:Word w)+(j.val:Word w)=((h.val*D+j.val:ℕ):Word w):=by push_cast;ring
          have read := (read_bank B.adjacency room.adjacency small m).trans
            (show m (B.adjacency.base+(h.val*D+j.val))=(number (near h ⟨j.val,live⟩):Word w) by
              simpa only [Nat.add_assoc] using data.adjacency h (⟨j.val,live⟩:Fin D))
          simpa [advance,Expr.eval,choice,old,ueq,number,DescriptorExpr.Comparison.test,castDiff,destDiff,times_at,RowOp.opcode,BinaryOp.eval,step,live,ptr] using read
      · have eqn : j.val=D:=by have:=j.isLt;omega
        simp [advance,Expr.eval,DescriptorExpr.Comparison.test,choice,old,number,step,eqn]
    · simpa only [body,walk,dite_eq_right active] using ih

theorem body_fits (B : Banks) (out : ℕ) (room : Fits B out H D w) (t : ℕ) : (body B H D t).Fits w out :=by
  induction t with
  | zero=>exact ⟨room.root,trivial⟩
  | succ t ih=>
    unfold body;split
    · exact ⟨⟨room.choice _,trivial⟩,trivial,ih,ih,trivial,trivial,room.adjacency,times_fits ih D,room.choice _,trivial⟩
    · exact ih

theorem body_work (B : Banks) (H D t : ℕ) : (body B H D t).work+10≤20*(D+10)^t :=by
  induction t with
  | zero=>simp [body,Expr.work]
  | succ t ih=>
    unfold body;split
    · simp only [advance,Expr.work,times_work,pow_succ]
      have lifted:=Nat.mul_le_mul_right (D+10) ih
      nlinarith
    · rw [pow_succ];nlinarith [Nat.mul_le_mul_right (D+10) ih]

theorem run (B : Banks) (out : ℕ) (room : Fits B out H D w) (near : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (data : Reads B near m) :
    let f:=body B H D 4
    let result:=image out (H*breadth D) f m
    (scan w out (H*breadth D) f).Exec m result (4+H*breadth D*(2*f.work+4)) ∧
      (∀v p,result (out+(row v p).val)=(number (walk near v (path p) 4):Word w)) ∧ CheapCode (scan w out (H*breadth D) f) :=by
  intro f result
  exact ⟨scan_exec _ _ _ _ (body_fits B out room 4) room.outside,
    fun v p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row v p)).trans (body_at B out room near m data v p 4),
    scan_cheap w out (H*breadth D) f⟩

end
end Hierarchy.DescentHaloWalkRAM

end OAI
