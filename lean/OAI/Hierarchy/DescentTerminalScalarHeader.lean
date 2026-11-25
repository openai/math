import OAI.Hierarchy.DescentTerminalControlBits

namespace OAI
/-! # Numeric local scalar headers in fixed bounded fields -/
namespace Hierarchy.DescentTerminalScalarHeader
open DescentKernelHistory DescentTerminalRowBooks DescentTerminalControlBits
open scoped Classical
noncomputable section

def ref {q H h : ℕ} (bound : h ≤ H) : Option (Fin q⊕Fin h)→Fin (q+H+1)
  | none=>0
  | some a=>(finSumFinEquiv (a.map id (Fin.castLE bound))).succ

def readRef {q H h : ℕ} : Fin (q+H+1)→Option (Fin q⊕Fin h) :=
  Fin.cases none (fun j=>match finSumFinEquiv.symm j with
    | .inl x=>some (.inl x)
    | .inr x=>if hx : x.val<h then some (.inr ⟨_,hx⟩) else none)

theorem ref_back {q H h : ℕ} (bound : h ≤ H) (x : Option (Fin q⊕Fin h)) :
    readRef (ref bound x)=x := by
  rcases x with _|a
  · rfl
  · rcases a with j|j <;> simp [readRef,ref,j.isLt]

def nodeRange (q t H A : ℕ) := t*((A+1)*(q+H+1)^A)+1
def bookRange (q t H N A w : ℕ) := (H+1)*((N+1)*((w+1)^H*(nodeRange q t H A)^N))
def range (q t H N A w V : ℕ) := (V+1)*(bookRange q t H N A w)^V

abbrev Node (q t h A : ℕ) := Option (Fin t×Fin (A+1)×(Fin A→Option (Fin q⊕Fin h)))
def node {q t H h A : ℕ} (bound : h ≤ H) : Node q t h A→Fin (nodeRange q t H A)
  | none=>⟨0,Nat.succ_pos _⟩
  | some (tag,arity,args)=>(finProdFinEquiv (tag,finProdFinEquiv (arity,
      finFunctionFinEquiv (fun j=>ref bound (args j))))).succ
def readNode {q t H h A : ℕ} : Fin (nodeRange q t H A)→Node q t h A :=
  Fin.cases none (fun code=>
    let z:=finProdFinEquiv.symm code
    let k:=finProdFinEquiv.symm z.2
    some (z.1,k.1,fun i=>readRef (finFunctionFinEquiv.symm k.2 i)))

theorem node_back {q t H h A : ℕ} (bound : h ≤ H) (x : Node q t h A) :
    readNode (node bound x)=x := by
  rcases x with _|⟨t,a,f⟩
  · rfl
  · simp only [readNode,node,Fin.cases_succ,Equiv.symm_apply_apply,ref_back]

def extend {n m : ℕ} {A : Type} (x : Fin n→A) (zero : A) (j : Fin m) : A :=
  if hj : j.val<n then x ⟨_,hj⟩ else zero

theorem extend_castLE {n m : ℕ} {A : Type} (x : Fin n→A) (zero : A) (hn : n ≤ m) (u : Fin n) :
    extend x zero (u.castLE hn) = x u := by
  unfold extend
  rw [dite_eq_left (show (u.castLE hn).val < n from u.isLt)]
  exact congrArg x (Fin.ext rfl)

def book {q t H N A w : ℕ} (b : Book q t H N A w) : Fin (bookRange q t H N A w) :=
  finProdFinEquiv (b.1,finProdFinEquiv (b.2.1,finProdFinEquiv
    (finFunctionFinEquiv (extend b.2.2.width 0 : Fin H→Fin (w+1)),
     finFunctionFinEquiv (extend (fun u=>node (Nat.le_of_lt_succ b.1.isLt) (b.2.2.rows u)) ⟨0,Nat.succ_pos _⟩ :
       Fin N→Fin (nodeRange q t H A)))))

def readBook {q t H N A w : ℕ} (j : Fin (bookRange q t H N A w)) : Book q t H N A w :=
  let b:=finProdFinEquiv.symm j
  let e:=finProdFinEquiv.symm b.2
  let cols:=finProdFinEquiv.symm e.2
  ⟨b.1,e.1,⟨fun u=>finFunctionFinEquiv.symm cols.1 (u.castLE (Nat.le_of_lt_succ b.1.isLt)),
    fun u=>readNode (finFunctionFinEquiv.symm cols.2 (u.castLE (Nat.le_of_lt_succ e.1.isLt)))⟩⟩

theorem book_back {q t H N A w : ℕ} (b : Book q t H N A w) : readBook (book b)=b := by
  rcases b with ⟨h,n,⟨width,rows⟩⟩
  let ww:Fin ((w+1)^H):=finFunctionFinEquiv (extend width 0)
  let nn:Fin ((nodeRange q t H A)^N):=finFunctionFinEquiv
    (extend (fun u=>node (Nat.le_of_lt_succ h.isLt) (rows u)) ⟨0,Nat.succ_pos _⟩)
  let fields (h₁:Fin (H+1)) (n₁:Fin (N+1)) (cs:Fin ((w+1)^H) × Fin ((nodeRange q t H A)^N)) :
      Book q t H N A w := ⟨h₁,n₁,⟨fun u=>finFunctionFinEquiv.symm cs.1 (u.castLE (Nat.le_of_lt_succ h₁.isLt)),
        fun u=>readNode (finFunctionFinEquiv.symm cs.2 (u.castLE (Nat.le_of_lt_succ n₁.isLt)))⟩⟩
  let mid (h₁:Fin (H+1)) (a:Fin (N+1) × Fin ((w+1)^H*(nodeRange q t H A)^N)) :=
    fields h₁ a.1 (finProdFinEquiv.symm a.2)
  let top (a:Fin (H+1) × Fin ((N+1)*((w+1)^H*(nodeRange q t H A)^N))) :=
    mid a.1 (finProdFinEquiv.symm a.2)
  change top (finProdFinEquiv.symm (finProdFinEquiv (h,finProdFinEquiv (n,finProdFinEquiv (ww,nn)))))=_
  rw [Equiv.symm_apply_apply]
  change mid h (finProdFinEquiv.symm (finProdFinEquiv (n,finProdFinEquiv (ww,nn))))=_
  rw [Equiv.symm_apply_apply]
  change fields h n (finProdFinEquiv.symm (finProdFinEquiv (ww,nn)))=_
  rw [Equiv.symm_apply_apply]
  simp only [fields,ww,nn,Equiv.symm_apply_apply,extend_castLE,node_back]

def emptyBook (q t H N A w : ℕ) : Book q t H N A w := ⟨0,0,⟨Fin.elim0,Fin.elim0⟩⟩

def encode {q t H N A w V : ℕ} (c : Control q t H N A w V) : Fin (range q t H N A w V) :=
  finProdFinEquiv (c.1,finFunctionFinEquiv (extend (fun j=>book (c.2 j))
    (book (emptyBook q t H N A w)) : Fin V→Fin (bookRange q t H N A w)))

def decode {q t H N A w V : ℕ} (j : Fin (range q t H N A w V)) : Control q t H N A w V :=
  let c:=finProdFinEquiv.symm j
  ⟨c.1,fun i=>readBook (finFunctionFinEquiv.symm c.2 (i.castLE (Nat.le_of_lt_succ c.1.isLt)))⟩

theorem back {q t H N A w V : ℕ} : Function.LeftInverse decode (encode (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)) := by
  rintro ⟨m,z⟩
  let packed : Fin ((bookRange q t H N A w)^V):=finFunctionFinEquiv
    (extend (fun j=>book (z j)) (book (emptyBook q t H N A w)))
  let unpack (p:Fin (V+1) × Fin ((bookRange q t H N A w)^V)) : Control q t H N A w V :=
    ⟨p.1,fun i=>readBook (finFunctionFinEquiv.symm p.2 (i.castLE (Nat.le_of_lt_succ p.1.isLt)))⟩
  change unpack (finProdFinEquiv.symm (finProdFinEquiv (m,packed)))=_
  rw [Equiv.symm_apply_apply]
  simp only [unpack,packed,Equiv.symm_apply_apply,extend_castLE,book_back]

private theorem prod {a b x y : ℕ} (one : a ≤ 2^x) (two : b ≤ 2^y) :
    a*b ≤ 2^(x+y) := by rw [pow_add]; exact Nat.mul_le_mul one two

private theorem power {a x : ℕ} (fit : a ≤ 2^x) (n : ℕ) : a^n ≤ 2^(n*x) := by
  simpa [pow_mul,Nat.mul_comm n x] using (Nat.pow_le_pow_left fit n)

/-- The integer alphabet has exactly the same conservative bit charge as
the original fieldwise descriptor estimate. Each padded zero is local and
constant, including the scalar with no hidden variables or atoms. -/
theorem book_range_room (q t H N A w size : ℕ) (ht : t≤2^size) :
    bookRange q t H N A w≤2^(bookBits q size H N A w) := by
  have leg (x : ℕ) : x ≤ 2^(lg x) := Nat.le_pow_clog (by decide) _
  have nd : nodeRange q t H A ≤ 2^(nodeBits q size H A) := by
    have live:=prod ht (prod (leg (A+1)) (power (leg (q+H+1)) A))
    have nz:=Nat.two_pow_pos (size+lg (A+1)+A*lg (q+H+1))
    rw [←Nat.add_assoc] at live
    unfold nodeRange nodeBits
    rw [pow_succ]
    omega
  exact prod (leg (H+1)) (prod (leg (N+1)) (prod (power (leg (w+1)) H) (power nd N)))

theorem header_room (q t H N A w V size : ℕ) (ht : t ≤ 2^size) :
    range q t H N A w V ≤ 2^(rowBits q size H N A w V) :=
  prod (Nat.le_pow_clog (by decide) (V+1)) (power (book_range_room q t H N A w size ht) V)

end
end Hierarchy.DescentTerminalScalarHeader

end OAI
