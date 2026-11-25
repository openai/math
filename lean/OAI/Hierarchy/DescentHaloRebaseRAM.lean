import OAI.Hierarchy.DescentHaloReversePath
import OAI.Hierarchy.DescentHaloRankRAM

namespace OAI
/-! # Rebase a truthful forward donor path using the common physical walk tables -/
namespace Hierarchy.DescentHaloWalkRAM.Rebase
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H D w : ℕ} (R : Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D

def terminal (v : Fin H) (p : Fin P):=number (walk R v (path p) 4)

def choose (u v : Fin H) : List (Fin P)→Option (Fin P)
  | []=>none
  | j::js=>if terminal R u j=v.val then some j else choose u v js

theorem choose_found (u v : Fin H) (js : List (Fin P)) (there : ∃i∈js,terminal R u i=v.val) :
    ∃i,choose R u v js=some i ∧ terminal R u i=v.val :=by
  induction js with
  | nil=>simp at there
  | cons a js ih=>
    by_cases hit : terminal R u a=v.val
    · exact ⟨a,by simp [choose,hit],hit⟩
    · obtain ⟨i,mem,withTarget⟩:=there
      have after : i∈js:=(List.mem_cons.mp mem).resolve_left (fun e=>hit (e ▸ withTarget))
      simpa only [choose,ite_eq_right hit] using ih ⟨i,after,withTarget⟩

structure Banks where
  endpoints : Bank
  ranks : Bank
  roots : Bank
  offsets : Bank

inductive Output | path | rank

def slot (mode : Output) (u : Fin H) (i : Fin P) : ℕ :=match mode with
  | .path=>i.val
  | .rank=>Ranks.earlier (terminal R) u (terminal R u i)

def value (mode : Output) (v : Fin H) (p : Fin P) : ℕ :=
  match walk R v (path p) 4 with
  | none=>P
  | some u=>(choose R u v (List.finRange P)).elim P (slot R mode u)

theorem value_le (mode : Output) (v : Fin H) (p : Fin P) : value R mode v p≤P :=by
  cases hit : walk R v (path p) 4 with
  | none => simp [value,hit]
  | some u =>
    cases selected : choose R u v (List.finRange P) with
    | none => simp [value,hit,selected]
    | some j =>
      simp only [value,hit,selected,Option.elim_some]
      cases mode with
      | path => exact j.isLt.le
      | rank => exact (Ranks.bound (terminal R) u j).le

def digit (mode : Output) (v : Fin H) (p : Fin P) : Fin (P+1):=⟨value R mode v p,Nat.lt_succ_of_le (value_le R mode v p)⟩

structure Fits (B : Banks) (out H D w : ℕ) : Prop where
  endpoints : B.endpoints.Fits w out
  ranks : B.ranks.Fits w out
  roots : B.roots.Fits w out
  offsets : B.offsets.Fits w out
  endCount : H*breadth D≤B.endpoints.size
  rankCount : H*breadth D≤B.ranks.size
  rootCount : H*breadth D≤B.roots.size
  offsetCount : H≤B.offsets.size
  sentinel : H<2^w
  output : out+H*breadth D<2^w

structure Reads (B : Banks) (m : Memory w) : Prop where
  ends : ∀(u : Fin H)(i : Fin P),m (B.endpoints.base+(row u i).val)=(terminal R u i:Word w)
  ranks : ∀(u : Fin H)(i : Fin P),m (B.ranks.base+(row u i).val)=(slot R .rank u i:Word w)
  roots : ∀(u : Fin H)(i : Fin P),m (B.roots.base+(row u i).val)=(u.val:Word w)
  offsets : ∀u : Fin H,m (B.offsets.base+u.val)=((u.val*P:ℕ):Word w)

def addr (B : Banks) (j : ℕ) : Expr :=.op .add (.lookup B.offsets (.lookup B.endpoints .row)) (.lit j)

def lookup (B : Banks) (mode : Output) : List (Fin P)→Expr
  | []=>.lit P
  | j::js=>.branch .eq (.lookup B.endpoints (addr B j.val)) (.lookup B.roots .row)
      (match mode with | .path=>.lit j.val | .rank=>.lookup B.ranks (addr B j.val)) (lookup B mode js)

def body (B : Banks) (mode : Output) (H D : ℕ) : Expr :=
  .branch .eq (.lookup B.endpoints .row) (.lit H) (.lit (breadth D)) (lookup B mode (List.finRange (breadth D)))

private theorem bank (b : Bank) {out i : ℕ} (ok : b.Fits w out) (hi : i<b.size) (m : Memory w) :
    b.read m (i:Word w)=m (b.base+i) :=by simp [Bank.read,Fin.val_cast_of_lt (hi.trans ok.2.1),Nat.mod_eq_of_lt hi]

theorem terminal_bound (v : Fin H) (p : Fin P) : terminal R v p≤H:=by unfold terminal number;cases walk R v (path p) 4 with | none=>exact le_rfl | some x=>exact x.isLt.le

theorem body_at (B : Banks) (mode : Output) (out : ℕ) (room : Fits B out H D w) (m : Memory w) (data : Reads R B m) (v : Fin H) (p : Fin P) :
    (body B mode H D).eval m ((row v p).val:Word w)=(value R mode v p:Word w):=by
  let r:=row v p
  have src :=(bank B.endpoints room.endpoints (r.isLt.trans_le room.endCount) m).trans (data.ends v p)
  cases reached : walk R v (path p) 4 with
  | none =>
    have sentinel : B.endpoints.read m ((row v p).val:Word w)=(H:Word w) := by
      simpa only [terminal,reached,number,Option.elim_none] using src
    simp [body,Expr.eval,DescriptorExpr.Comparison.test,sentinel,reached,value]
  | some u=>
    have dst : B.endpoints.read m ((row v p).val:Word w)=(u.val:Word w):=by simpa only [terminal,reached,number,Option.elim_some] using src
    have nonsentinel : (u.val:Word w)≠(H:Word w):=by
      intro eqn;have:=congrArg Fin.val eqn;rw [Fin.val_cast_of_lt (u.isLt.trans room.sentinel),Fin.val_cast_of_lt room.sentinel] at this;exact u.isLt.ne this
    have base:=(bank B.offsets room.offsets (u.isLt.trans_le room.offsetCount) m).trans (data.offsets u)
    have root:=(bank B.roots room.roots (r.isLt.trans_le room.rootCount) m).trans (data.roots v p)
    have ptr (j : Fin P) : (addr B j.val).eval m (r.val:Word w)=((row u j).val:Word w):=by
      change B.offsets.read m (B.endpoints.read m (r.val:Word w))+(j.val:Word w)=_
      rw [dst,base,←Nat.cast_add];congr 1;simp [row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have read (js : List (Fin P)) : (lookup B mode js).eval m (r.val:Word w)=(((choose R u v js).elim P (slot R mode u):ℕ):Word w):=by
      induction js with
      | nil=>rfl
      | cons j js ih=>
        have near : B.endpoints.read m ((row u j).val:Word w)=(terminal R u j:Word w):=
          (bank B.endpoints room.endpoints ((row u j).isLt.trans_le room.endCount) m).trans (data.ends u j)
        have rank : B.ranks.read m ((row u j).val:Word w)=(slot R .rank u j:Word w):=
          (bank B.ranks room.ranks ((row u j).isLt.trans_le room.rankCount) m).trans (data.ranks u j)
        have eqn : ((terminal R u j:Word w)=(v.val:Word w)) ↔ terminal R u j=v.val:=by
          constructor
          · intro same;have h:=congrArg Fin.val same
            rw [Fin.val_cast_of_lt ((terminal_bound R u j).trans_lt room.sentinel),Fin.val_cast_of_lt (v.isLt.trans room.sentinel)] at h;exact h
          · exact fun same=>congrArg (fun n:ℕ=>(n:Word w)) same
        by_cases yes : terminal R u j=v.val <;> cases mode <;>
          simp [lookup,Expr.eval,ptr,root,near,rank,DescriptorExpr.Comparison.test,choose,yes,eqn,slot,ih]
    simpa [body,Expr.eval,DescriptorExpr.Comparison.test,dst,nonsentinel,reached,value,r] using read (List.finRange P)

private theorem addr_fits (B : Banks) {out} (ok : Fits B out H D w) (j : ℕ) : (addr B j).Fits w out :=⟨⟨ok.offsets,ok.endpoints,trivial⟩,trivial⟩

theorem body_fits (B : Banks) (mode : Output) {out} (ok : Fits B out H D w) : (body B mode H D).Fits w out:=by
  have sub (xs : List (Fin P)) : (lookup B mode xs).Fits w out:=by
    induction xs with
    | nil=>trivial
    | cons j js ih=>refine ⟨⟨ok.endpoints,addr_fits B ok _⟩,⟨ok.roots,trivial⟩,?_,ih⟩;cases mode with | path=>trivial | rank=>exact ⟨ok.ranks,addr_fits B ok _⟩
  exact ⟨⟨ok.endpoints,trivial⟩,trivial,trivial,sub _⟩

theorem body_work (B : Banks) (mode : Output) (H D : ℕ) : (body B mode H D).work≤16+64*breadth D:=by
  have size (xs : List (Fin (breadth D))) : (lookup B mode xs).work≤1+64*xs.length:=by
    induction xs with
    | nil=>simp [lookup,Expr.work]
    | cons j js ih=>cases mode <;> simp only [lookup,addr,Expr.work,List.length_cons] at * <;> omega
  have bound:=size (List.finRange (breadth D));simp only [List.length_finRange] at bound
  unfold body;simp only [Expr.work];omega

theorem run (B : Banks) (mode : Output) (out : ℕ) (room : Fits B out H D w) (m : Memory w) (data : Reads R B m) :
    let f:=body B mode H D
    let result:=image out (H*P) f m
    (scan w out (H*P) f).Exec m result (4+H*P*(2*f.work+4)) ∧
      (∀v p,result (out+(row v p).val)=(value R mode v p:Word w)) ∧ CheapCode (scan w out (H*P) f):=by
  intro f result;exact ⟨scan_exec _ _ _ _ (body_fits B mode room) room.output,
    fun v p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row v p)).trans (body_at R B mode out room m data v p),by apply scan_cheap⟩

/-- The forward true old-source route is all that is needed in the raw row.
The reverse path and actual rank in the new source's roster are both present
in the shared output table at the same bounded forward-path ordinal. -/
theorem actual (reciprocal : ∀v u i,R v i=some u→∃j,R u j=some v) (v u : Fin H) (p : Fin P) (hit : walk R v (path p) 4=some u) :
    ∃q : Fin P,walk R u (path q) 4=some v ∧ value R .path v p=q.val ∧ value R .rank v p=Ranks.earlier (terminal R) u v.val:=by
  obtain ⟨back,there⟩:=reverse_path R reciprocal _ v u hit
  let j : Fin P:=finFunctionFinEquiv back
  have test : terminal R u j=v.val:=by simp [terminal,path,j,there,number]
  obtain ⟨q,selected,equ⟩:=choose_found R u v (List.finRange P) ⟨j,List.mem_finRange j,test⟩
  refine ⟨q,?_,by simp [value,hit,selected,slot],by simp [value,hit,selected,slot,equ]⟩
  cases seen : walk R u (path q) 4 with
  | none =>
    have impossible : H=v.val := by simpa [terminal,seen,number] using equ
    exact False.elim (v.isLt.ne impossible.symm)
  | some t =>
    have same : t.val=v.val := by simpa [terminal,seen,number] using equ
    exact congrArg some (Fin.ext same)

end
end Hierarchy.DescentHaloWalkRAM.Rebase

end OAI
