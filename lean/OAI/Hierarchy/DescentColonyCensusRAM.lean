import OAI.Hierarchy.DescentColonyFinScan
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native leaf-key recovery and exact census on the installed split banks -/

noncomputable section
namespace Hierarchy.DescentColonies.CensusRAM

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM ProtocolRAM Scan
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing

variable {k H w : ℕ}

private def get (addr : ℕ) : Expr := .lookup ⟨addr,0⟩ (.lit 0)

private theorem get_eval (addr : ℕ) (m : Memory w) (r : Word w) : (get addr).eval m r=m addr := by
  simp [get,Expr.eval,Bank.read,Bank.size]

/-- Walk the row for one physical block in increasing depth and emit either
component of its first unsplit key. -/
def follow (atWord value : ℕ → ℕ) : ℕ → ℕ → Expr
  | 0,d => .lit (value d)
  | rem+1,d => .branch .eq (get (atWord d)) (.lit 0) (.lit (value d))
      (follow atWord value rem (d+1))

theorem follow_eval (atWord value : ℕ→ℕ) (split : ℕ→Bool) (m : Memory w) (r : Word w)
    (rem d : ℕ) (wide : 1<2^w) (reads : ∀j,d≤j → j<d+rem → m (atWord j)=((split j).toNat:Word w)) :
    (follow atWord value rem d).eval m r=(value (seek split rem d).1:Word w) := by
  have nz : (1:Word w)≠0 := by
    intro h
    have hh := congrArg Fin.val h
    change (1:ℕ)%(2^w)=0 at hh
    rw [Nat.mod_eq_of_lt wide] at hh
    omega
  induction rem generalizing d with
  | zero => rfl
  | succ rem ih =>
    have read := reads d le_rfl (by omega)
    have later := ih (d+1) (fun j lo hi => reads j (by omega) (by omega))
    cases h : split d <;> simp [follow,Expr.eval,Comparison.test,get_eval,read,h,nz,seek,later]

private theorem follow_fits (atWord value : ℕ→ℕ) (rem d out : ℕ)
    (wide : 1<2^w) (below : ∀j,d≤j → j<d+rem → atWord j<out) :
    (follow atWord value rem d).Fits w out := by
  induction rem generalizing d with
  | zero => trivial
  | succ rem ih =>
    exact ⟨⟨⟨Nat.two_pow_pos _,wide,Nat.succ_le_of_lt (below d le_rfl (by omega))⟩,trivial⟩,trivial,
      trivial,ih _ (fun j lo hi => below _ (by omega) (by omega))⟩

theorem follow_work (atWord value : ℕ→ℕ) (rem d : ℕ) :
    (follow atWord value rem d).work=1+9*rem := by
  induction rem generalizing d with
  | zero => rfl
  | succ rem ih => simp only [follow,get,Expr.work,ih,Nat.mul_succ]; omega

abbrev Keys := Expr×Expr

def key (banks : ℕ→Fin H→ℕ) (v : Fin H) (x : Block k) : Keys :=
  let atWord := fun d => banks d v+x.val
  (follow atWord id k 0,follow atWord (fun d=>group d x) k 0)

private def evaluated (m : Memory w) (r : Word w) (x : Keys) : ℕ×ℕ :=
  ((x.1.eval m r).val,(x.2.eval m r).val)

private theorem seek_bound (s : ℕ→Bool) (rem d : ℕ) : (seek s rem d).1 ≤ d+rem := by
  induction rem generalizing d with
  | zero => simp [seek]
  | succ rem ih => simp only [seek]; split <;> first | exact (ih _).trans_eq (by omega) | omega

private theorem key_eval (banks : ℕ→Fin H→ℕ) (v : Fin H) (x : Block k)
    (rows : Buffer (Fin H) k) (m : Memory w) (r : Word w) (wide : 1<2^w) (bits : k<2^w)
    (room : 2^k≤2^w)
    (source : ∀d<k,m (banks d v+x.val)=((lookup rows d v x).toNat:Word w)) :
    evaluated m r (key banks v x)=(leafDepth rows v x,group (leafDepth rows v x) x) := by
  have read (d : ℕ) (_ : 0≤d) (hi : d<0+k) := source d (by omega)
  have depth : leafDepth rows v x≤k := by simpa [leafDepth] using seek_bound (fun d=>lookup rows d v x) k 0
  have name : group (leafDepth rows v x) x < 2^w :=
    (Nat.div_le_self x.val _).trans_lt (x.isLt.trans_le room)
  simp only [evaluated,key,follow_eval _ _ _ m r k 0 wide read,Function.id_def]
  change (((leafDepth rows v x : Word w).val), ((group (leafDepth rows v x) x : Word w).val)) = _
  rw [Fin.val_cast_of_lt (depth.trans_lt bits),Fin.val_cast_of_lt name]

private def eqKey (a b : Keys) : Expr :=
  .branch .eq a.1 b.1 (.branch .eq a.2 b.2 (.lit 1) (.lit 0)) (.lit 0)

private theorem eqKey_eval (a b : Keys) (m : Memory w) (r : Word w) :
    (eqKey a b).eval m r=if evaluated m r a=evaluated m r b then 1 else 0 := by
  simp only [eqKey,evaluated,Expr.eval,Comparison.test,beq_iff_eq,Prod.mk.injEq]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- Test whether the current occurrence has another copy of its leaf key later
on the same site. Each suffix comparison is compiled once. -/
private def fresh (a : Keys) : List Keys → Expr
  | [] => .lit 1
  | b::bs => .branch .eq (eqKey b a) (.lit 1) (.lit 0) (fresh a bs)

private theorem fresh_eval (a : Keys) (bs : List Keys) (m : Memory w) (r : Word w)
    (nz : (1:Word w)≠0) :
    (fresh a bs).eval m r = if (containsKey (evaluated m r a) (bs.map (evaluated m r))).1 then 0 else 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hit : evaluated m r b=evaluated m r a <;>
      simp [fresh,Expr.eval,Comparison.test,eqKey_eval,hit,containsKey,Ne.symm nz,ih]

private def count : List Keys → Expr
  | [] => .lit 0
  | a::as => .op .add (count as) (fresh a as)

private theorem count_eval (ps : List Keys) (m : Memory w) (r : Word w) (nz : (1:Word w)≠0) :
    (count ps).eval m r = ((uniqueIDs (ps.map (evaluated m r))).1:Word w) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [count,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,fresh_eval _ _ m r nz,List.map_cons,uniqueIDs]
    split <;> simp

private def total : List Expr → Expr
  | [] => .lit 0
  | a::as => .op .add a (total as)

private theorem total_eval (ps : List Expr) (m : Memory w) (r : Word w) :
    (total ps).eval m r=(ps.map (fun e=>e.eval m r)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

def expression (k : ℕ) (banks : ℕ→Fin H→ℕ) : Expr :=
  total (List.ofFn fun v=>count (List.ofFn (key (k:=k) banks v)))

theorem eval (banks : ℕ→Fin H→ℕ) (incoming : Fin H→List (Fin H)) (load : Fin H→Block k→ℕ)
    (D cap : ℕ) (m : Memory w) (r : Word w) (wide : 1<2^w) (bits : k<2^w) (room : 2^k≤2^w)
    (source : ∀d<k,∀v x,m (banks d v+x.val)=((lookup (build incoming load D cap k) d v x).toNat:Word w)) :
    (expression k banks).eval m r=(FinRows.score incoming load D cap:Word w) := by
  let rows := build incoming load D cap k
  have nz : (1:Word w)≠0 := by
    intro h
    have hh := congrArg Fin.val h
    change (1:ℕ)%(2^w)=0 at hh
    rw [Nat.mod_eq_of_lt wide] at hh
    omega
  have site (v : Fin H) : (count (List.ofFn (key (k:=k) banks v))).eval m r =
      ((uniqueIDs (keyList rows v)).1:Word w) := by
    rw [count_eval _ _ _ nz,List.map_ofFn]
    have eq : (evaluated m r) ∘ (key (k:=k) banks v) =
        (fun x=> (leafDepth rows v x,group (leafDepth rows v x) x)) :=
      funext fun x => key_eval banks v x rows m r wide bits room (fun d hd=>source d hd v x)
    rw [eq]
    rfl
  rw [expression,total_eval,List.map_ofFn,List.sum_ofFn,FinRows.score_eq_leafScore,leafScore,Nat.cast_sum]
  exact Finset.sum_congr rfl fun v _=>site v

private theorem fits_fresh {out : ℕ} (a : Keys) (as : List Keys)
    (h : a.1.Fits w out ∧ a.2.Fits w out) (hs : ∀p∈as,p.1.Fits w out ∧ p.2.Fits w out) :
    (fresh a as).Fits w out := by
  induction as with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨u,v⟩ := hs b List.mem_cons_self
    exact ⟨⟨u,h.1,⟨v,h.2,trivial,trivial⟩,trivial⟩,trivial,trivial,ih (fun p hp=>hs p (List.mem_cons_of_mem _ hp))⟩

private theorem fits_count {out : ℕ} (as : List Keys) (hs : ∀p∈as,p.1.Fits w out ∧ p.2.Fits w out) :
    (count as).Fits w out := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    have rest := fun p hp=>hs p (List.mem_cons_of_mem a hp)
    exact ⟨ih rest,fits_fresh _ _ (hs a List.mem_cons_self) rest⟩

private theorem fits_total {out : ℕ} (ps : List Expr) (h : ∀e∈ps,e.Fits w out) : (total ps).Fits w out := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨h p List.mem_cons_self,ih (fun q hq=>h q (List.mem_cons_of_mem _ hq))⟩

theorem fits (banks : ℕ→Fin H→ℕ) (out : ℕ) (wide : 1<2^w)
    (below : ∀d<k,∀v,banks d v+2^k≤out) : (expression k banks).Fits w out := by
  apply fits_total
  intro p hp
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hp
  apply fits_count
  intro pair hp
  obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hp
  have addr : ∀ j, 0≤j → j<0+k → banks j v+x.val<out :=
    fun j _ hj => (Nat.add_lt_add_left x.isLt _).trans_le (below _ (by omega) _)
  exact ⟨follow_fits _ _ _ _ _ wide addr,follow_fits _ _ _ _ _ wide addr⟩

private def KeyBound (A : ℕ) (p : Keys) := p.1.work≤A ∧ p.2.work≤A

private theorem eqKey_work {A : ℕ} {a b : Keys} (ha : KeyBound A a) (hb : KeyBound A b) :
    (eqKey a b).work ≤ 4*A+5 := by
  rcases ha with ⟨a₁,a₂⟩
  rcases hb with ⟨b₁,b₂⟩
  simp only [eqKey,Expr.work]
  omega

private theorem fresh_work {A : ℕ} (a : Keys) (as : List Keys) (ha : KeyBound A a)
    (hs : ∀p∈as,KeyBound A p) : (fresh a as).work ≤ 1+as.length*(4*A+8) := by
  induction as with
  | nil => simp [fresh,Expr.work]
  | cons b bs ih =>
    have e := eqKey_work (hs _ List.mem_cons_self) ha
    have f := ih (fun p hp=>hs _ (List.mem_cons_of_mem _ hp))
    simp only [fresh,Expr.work,List.length_cons,Nat.succ_mul bs.length (4*A+8)]
    omega

private theorem count_work {A : ℕ} (as : List Keys) (hs : ∀p∈as,KeyBound A p) :
    (count as).work ≤ 1+as.length*(2+as.length*(4*A+8)) := by
  induction as with
  | nil => simp [count,Expr.work]
  | cons b bs ih =>
    have old := fun p hp=>hs p (List.mem_cons_of_mem b hp)
    have tailWork := ih old
    have freshWork := fresh_work b bs (hs _ List.mem_cons_self) old
    let n := bs.length
    let fee := 4*A+8
    calc
      (count (b::bs)).work ≤ (1+n*(2+n*fee))+(1+n*fee)+1 :=
        Nat.add_le_add_right (Nat.add_le_add tailWork freshWork) 1
      _ ≤ ((1+n*(2+n*fee))+(1+n*fee)+1)+(n+1)*fee := Nat.le_add_right _ _
      _ = 1+(b::bs).length*(2+(b::bs).length*(4*A+8)) := by
        change _ = 1+(n+1)*(2+(n+1)*fee)
        ring

private theorem total_work (ps : List Expr) (c : ℕ) (h : ∀e∈ps,e.work≤c) :
    (total ps).work ≤ 1+ps.length*(c+1) := by
  induction ps with
  | nil => simp [total,Expr.work]
  | cons a as ih =>
    have ea := h _ List.mem_cons_self
    have tail := ih (fun e he=>h _ (List.mem_cons_of_mem _ he))
    simp only [total,Expr.work,List.length_cons,Nat.succ_mul]
    omega

def workBound (H k : ℕ) := 1+H*(2+2^k*(2+2^k*(4*(1+9*k)+8)))

theorem work (banks : ℕ→Fin H→ℕ) : (expression k banks).work ≤ workBound H k := by
  let c := 1+2^k*(2+2^k*(4*(1+9*k)+8))
  have one (v : Fin H) : (count (List.ofFn (key (k:=k) banks v))).work ≤ c := by
    have keys (p : Keys) (h : p ∈ List.ofFn (key (k:=k) banks v)) : KeyBound (1+9*k) p := by
      obtain ⟨x,rfl⟩ := List.mem_ofFn.mp h
      exact ⟨(follow_work _ _ k 0).le,(follow_work _ _ k 0).le⟩
    simpa only [List.length_ofFn,c] using count_work _ keys
  have all := total_work (List.ofFn fun v=>count (List.ofFn (key (k:=k) banks v))) c (by
    intro p hp
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hp
    exact one v)
  have step (n : ℕ) : 1+n+1=2+n := by omega
  simpa only [expression,List.length_ofFn,c,workBound,step] using all

def program (w k out : ℕ) (banks : ℕ→Fin H→ℕ) := scan w out 1 (expression k banks)

def after (k out : ℕ) (banks : ℕ→Fin H→ℕ) (m : Memory w) := image out 1 (expression k banks) m

theorem run (out : ℕ) (banks : ℕ→Fin H→ℕ) (m : Memory w)
    (fit : out+1<2^w) (below : ∀d<k,∀v,banks d v+2^k≤out) :
    (program w k out banks).Exec m (after k out banks m) (4+1*(2*(expression k banks).work+4)) :=
  scan_exec _ _ _ _ (fits banks out (by omega) below) fit

theorem published (out : ℕ) (banks : ℕ→Fin H→ℕ) (incoming : Fin H→List (Fin H))
    (load : Fin H→Block k→ℕ) (D cap : ℕ) (m : Memory w) (wide : 1<2^w) (bits : k<2^w)
    (room : 2^k≤2^w)
    (source : ∀d<k,∀v x,m (banks d v+x.val)=((lookup (build incoming load D cap k) d v x).toNat:Word w)) :
    after k out banks m out=(FinRows.score incoming load D cap:Word w) := by
  simpa [after] using (ProtocolRAMGeneratedWrite.read_image out 1 (expression k banks) m (0:Fin 1)).trans
    (eval banks incoming load D cap m 0 wide bits room source)

end Hierarchy.DescentColonies.CensusRAM

end
end OAI
