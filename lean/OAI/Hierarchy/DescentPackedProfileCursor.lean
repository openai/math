import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Packed output positions from one carry per measured chunk -/

namespace Hierarchy.DescentPacking.PackedProfileCursor
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

def addr (out i : ℕ) := out+2*i
def get (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)

def step (R counts out i : ℕ) : Expr :=
  let q := get (addr out i)
  let add := .op .add (get (addr out i+1)) (get (counts+i))
  let ended := .op .sub add (.lit R)
  .branch .eq .row (.lit 0)
    (.branch .lt add (.lit R) q (.op .add q (.lit 1)))
    (.branch .lt add (.lit R) add ended)

def passes (R counts out : ℕ) : ℕ→List Pass
  | 0 => [⟨out,2,.lit 0⟩]
  | n+1 => passes R counts out n++[⟨addr out (n+1),2,step R counts out n⟩]

def program (w R counts out n : ℕ) := ProtocolRAM.program w (passes R counts out n)
def after {w : ℕ} (R counts out n : ℕ) (m : Memory w) := result (passes R counts out n) m
def ticks (n : ℕ) := clock (passes 0 0 0 n)

private theorem allowed {R counts out n : ℕ} (p : Pass) (h : p∈passes R counts out n) :
    out≤p.out ∧ p.out+p.rows≤addr out n+2 ∧ p.rows=2 ∧
    p.term.inputEnd ≤ max (counts+n) p.out ∧ p.term.work≤100 := by
  induction n with
  | zero =>
    simp only [passes,List.mem_singleton] at h
    subst p
    simp [addr,Expr.inputEnd,Expr.work]
  | succ n ih =>
    rcases List.mem_append.mp h with h|h
    · obtain ⟨a,b,c,d,e⟩ := ih h
      exact ⟨a,by dsimp [addr] at *;omega,c,d.trans (by omega),e⟩
    · rw [List.mem_singleton] at h
      subst p
      simp [step,get,addr,Expr.inputEnd,Bank.size,Expr.work]; omega

theorem cheap (w R counts out n : ℕ) : CheapCode (program w R counts out n) :=
  program_cheap w (passes R counts out n)

private theorem clock_last (ps : List Pass) (p : Pass) : clock (ps++[p])=clock ps+p.clock := by
  induction ps with
  | nil => simp [clock,Nat.add_comm]
  | cons a ps ih => simp only [List.cons_append,clock,ih];omega

private theorem fixed (R counts out n : ℕ) : clock (passes R counts out n)=ticks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change clock (_++[_])=clock (_++[_])
    rw [clock_last,clock_last,ih]
    rfl

theorem ticks_bound (n : ℕ) : ticks n≤4+412*(n+1) := by
  have len (i : ℕ) : (passes 0 0 0 i).length=i+1 := by induction i <;> simp_all [passes]
  simpa only [ticks,len,Nat.mul_comm (n+1)] using
    clock_le (passes 0 0 0 n) 2 100 (fun p hp => ⟨(allowed p hp).2.2.1.le,(allowed p hp).2.2.2.2⟩)

theorem run {w : ℕ} (R counts out n : ℕ) (m : Memory w) (apart : counts+n≤out) (room : addr out n+2<2^w) :
    (program w R counts out n).Exec m (after R counts out n m) (ticks n) := by
  rw [←fixed R counts out n]
  apply program_exec
  intro p hp
  obtain ⟨lo,hi,_,bound,_⟩ := allowed p hp
  exact p.fits_of_span (bound.trans (max_le (apart.trans lo) le_rfl)) (hi.trans_lt room)

theorem below {w : ℕ} (R counts out n : ℕ) (m : Memory w) (a : ℕ) (low : a<out) :
    after R counts out n m a=m a :=
  result_below _ m a fun p hp=>low.trans_le (allowed p hp).1

theorem above {w : ℕ} (R counts out n : ℕ) (m : Memory w) (a : ℕ)
    (bound : addr out n+2≤a) : after R counts out n m a=m a := by
  have outside (ps : List Pass) (mem : Memory w) (safe : ∀p∈ps,p.out+p.rows≤a) :
      result ps mem a=mem a := by
    induction ps generalizing mem with
    | nil=>rfl
    | cons p ps ih=>
      exact (ih (p.apply mem) (fun t ht=>safe t (List.mem_cons_of_mem _ ht))).trans
        (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (safe p (List.mem_cons_self ..))))
  exact outside _ m (fun p hp=>((allowed p hp).2.1).trans bound)

def total (amount : ℕ→ℕ) : ℕ→ℕ
  | 0=>0
  | i+1=>total amount i+amount i

private theorem carry {x a R : ℕ} (h : 0<R) (small : a≤R) :
    let sum := x%R+a
    (if sum<R then x/R else x/R+1)=(x+a)/R ∧
    (if sum<R then sum else sum-R)=(x+a)%R := by
  dsimp
  have rep := Nat.mod_add_div x R
  have lt := Nat.mod_lt x h
  by_cases stay : x%R+a<R
  · have eqn : x+a=R*(x/R)+(x%R+a) := by omega
    simp [stay,eqn,Nat.mul_add_div h,Nat.div_eq_of_lt stay,Nat.mod_eq_of_lt stay]
  · have rest : x%R+a-R<R := by omega
    have eqn : x+a=R*(x/R+1)+(x%R+a-R) := by rw [Nat.mul_succ];omega
    simp [stay,eqn,Nat.mul_add_div h,Nat.div_eq_of_lt rest,Nat.mod_eq_of_lt rest]

open DescriptorExpr in
private theorem eval {w : ℕ} (R counts out i x a : ℕ) (m : Memory w) (j : Fin 2)
    (hR : 0<R) (small : a≤R) (width : 2*R≤2^w)
    (q : m (addr out i)=(x/R:ℕ)) (r : m (addr out i+1)=(x%R:ℕ)) (rd : m (counts+i)=(a:Word w)) :
    (step R counts out i).eval m (j.val:Word w)=
      if j.val=0 then ((x+a)/R:ℕ) else ((x+a)%R:ℕ) := by
  have bound := Nat.mod_lt x hR
  have whole : x%R+a<2^w := by omega
  have rb : R<2^w := by omega
  have wordSum : ((x%R:ℕ):Word w)+(a:Word w)=((x%R+a:ℕ):Word w) := (Nat.cast_add ..).symm
  have cmp : (((x%R+a:ℕ):Word w)<(R:Word w)) ↔ x%R+a<R := by
    change (((x%R+a:ℕ):Word w).val < (R:Word w).val) ↔ _
    rw [Fin.val_cast_of_lt whole,Fin.val_cast_of_lt rb]
  have piece := carry (x:=x) hR small
  have minus (no : ¬x%R+a<R) : ((x%R+a:ℕ):Word w)-(R:Word w)=((x%R+a-R:ℕ):Word w) :=
    (Nat.cast_sub (Nat.le_of_not_gt no)).symm
  have one : (1:Word w)≠0 := by
    intro same
    have u := congrArg Fin.val same
    change (1:ℕ)%2^w=0 at u
    rw [Nat.mod_eq_of_lt (by omega)] at u
    contradiction
  have quotient : (if x%R+a<R then ((x/R:ℕ):Word w) else ((x/R:ℕ):Word w)+1) =
      (((x+a)/R:ℕ):Word w) := by
    by_cases stay : x%R+a<R <;>
      simpa only [stay,ite_true,ite_false,Nat.cast_add,Nat.cast_one] using
        congrArg (fun t : ℕ => (t : Word w)) piece.1
  have remainder : (if x%R+a<R then ((x%R+a:ℕ):Word w) else ((x%R+a:ℕ):Word w)-(R:Word w)) =
      (((x+a)%R:ℕ):Word w) := by
    by_cases stay : x%R+a<R
    · simpa only [stay,ite_true] using congrArg (fun t : ℕ => (t : Word w)) piece.2
    · simpa only [stay,ite_false,minus stay] using congrArg (fun t : ℕ => (t : Word w)) piece.2
  have row_value (row : Word w) : (step R counts out i).eval m row =
      if row=0 then (((x+a)/R:ℕ):Word w) else (((x+a)%R:ℕ):Word w) := by
    simp only [step,get,Expr.eval,Bank.read,Bank.size,Nat.pow_zero,Nat.mod_one,Nat.add_zero,
      RowOp.opcode,BinaryOp.eval,Comparison.test,beq_iff_eq,decide_eq_true_eq,q,r,rd,wordSum,cmp,
      Nat.cast_zero,Nat.cast_one,quotient,remainder]
  fin_cases j
  · change (step R counts out i).eval m 0 = (((x+a)/R:ℕ):Word w)
    exact (row_value 0).trans (ite_eq_left rfl)
  · change (step R counts out i).eval m 1 = (((x+a)%R:ℕ):Word w)
    exact (row_value 1).trans (ite_eq_right one)

theorem read {w : ℕ} (R counts out n : ℕ) (m : Memory w) (amount : ℕ→ℕ)
    (positive : 0<R) (width : 2*R≤2^w) (apart : counts+n≤out)
    (source : ∀i<n,m (counts+i)=(amount i:Word w)) (small : ∀i<n,amount i≤R) :
    ∀i≤n, after R counts out n m (addr out i)=((total amount i/R:ℕ):Word w) ∧
      after R counts out n m (addr out i+1)=((total amount i%R:ℕ):Word w) := by
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i=0 := by omega
    constructor
    · exact (ProtocolRAMGeneratedWrite.read_image out 2 (.lit 0) m (0:Fin 2)).trans (by simp [total,Expr.eval])
    · exact (ProtocolRAMGeneratedWrite.read_image out 2 (.lit 0) m (1:Fin 2)).trans (by simp [total,Expr.eval])
  | succ n ih =>
    let prev := after R counts out n m
    let next := addr out (n+1)
    have earlier := ih (by omega) (fun i hi=>source i (by omega)) (fun i hi=>small i (by omega))
    have eqn : after R counts out (n+1) m=image next 2 (step R counts out n) prev := by
      unfold after
      rw [passes,result_append]
      rfl
    intro i hi
    rw [eqn]
    by_cases old : i≤n
    · have t := earlier i old
      exact ⟨(ProtocolRAMGeneratedWrite.frame_image _ _ _ prev _ (.inl (by dsimp [next,addr];omega))).trans t.1,
        (ProtocolRAMGeneratedWrite.frame_image _ _ _ prev _ (.inl (by dsimp [next,addr];omega))).trans t.2⟩
    · obtain rfl : i=n+1 := by omega
      obtain ⟨q,r⟩ := earlier n le_rfl
      have raw : prev (counts+n)=(amount n:Word w) :=
        (below _ _ _ _ _ _ (by omega)).trans (source n (by omega))
      have value := eval R counts out n (total amount n) (amount n) prev
      exact ⟨(ProtocolRAMGeneratedWrite.read_image next 2 _ prev (0:Fin 2)).trans
          (value 0 positive (small n (by omega)) width q r raw),
        (ProtocolRAMGeneratedWrite.read_image next 2 _ prev (1:Fin 2)).trans
          (value 1 positive (small n (by omega)) width q r raw)⟩

theorem total_le {R n : ℕ} (amount : ℕ→ℕ) (small : ∀i<n,amount i≤R) : total amount n≤n*R := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total,Nat.succ_mul]
    exact Nat.add_le_add (ih (fun i hi=>small i (by omega))) (small n (by omega))

/-- Both fields decode to mathematical integers, including after prefix totals
larger than a word. The quotient is bounded by the number of chunks. -/
theorem values {w : ℕ} (R counts out n : ℕ) (m : Memory w) (amount : ℕ→ℕ)
    (positive : 0<R) (width : 2*R≤2^w) (apart : counts+n≤out) (room : addr out n+2<2^w)
    (source : ∀i<n,m (counts+i)=(amount i:Word w)) (small : ∀i<n,amount i≤R) (i : ℕ) (hi : i≤n) :
    (after R counts out n m (addr out i)).val=total amount i/R ∧
    (after R counts out n m (addr out i+1)).val=total amount i%R := by
  obtain ⟨q,r⟩ := read R counts out n m amount positive width apart source small i hi
  have totalBound := total_le (n:=i) amount (fun j hj=>small j (hj.trans_le hi))
  have bins : total amount i/R≤ i := (Nat.div_le_iff_le_mul positive).2 (by omega)
  rw [q,r,Fin.val_cast_of_lt (by dsimp [addr] at room;omega : total amount i/R<2^w),
    Fin.val_cast_of_lt ((Nat.mod_lt _ positive).trans_le (by omega):total amount i%R<2^w)]
  exact ⟨rfl,rfl⟩

theorem size (w R counts out n : ℕ) :
    (program w R counts out n).labels≤10+307*(n+1) ∧
    (program w R counts out n).registers≤5+104*(n+1) ∧ (program w R counts out n).slots=0 := by
  let ps := passes R counts out n
  obtain ⟨labels,regs,slots⟩ := program_size w ps
  have sum_le (xs : List Pass) (g : Pass→ℕ) (k : ℕ) (bound : ∀p∈xs,g p≤k) :
      (xs.map g).sum≤xs.length*k := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have a := bound x (by simp)
      have b := ih (fun p hp=>bound p (by simp [hp]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      omega
  have length (i : ℕ) : (passes R counts out i).length=i+1 := by induction i <;> simp_all [passes]
  have a := sum_le ps (fun p=>7+3*p.term.work) 307 (fun p hp=>by have := (allowed p hp).2.2.2.2;omega)
  have b := sum_le ps (fun p=>4+p.term.work) 104 (fun p hp=>by have := (allowed p hp).2.2.2.2;omega)
  have len : ps.length=n+1 := length n
  exact ⟨labels.le.trans (Nat.add_le_add_left (a.trans_eq (by rw [len,Nat.mul_comm])) _),
    regs.le.trans (Nat.add_le_add_left (b.trans_eq (by rw [len,Nat.mul_comm])) _),slots⟩

end Hierarchy.DescentPacking.PackedProfileCursor

end OAI
