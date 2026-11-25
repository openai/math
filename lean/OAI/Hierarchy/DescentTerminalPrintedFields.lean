import OAI.Hierarchy.DescentTerminalChronologicalBooks

namespace OAI
/-! # Six bounded numeric leaf columns of one physical scalar descriptor -/
namespace Hierarchy.DescentTerminalPrintedFields
open DescentKernelHistory DescentTerminalRowBooks DescentTerminalScalarHeader DescentTerminalControlBits
open scoped Classical
noncomputable section
variable {q t H N A w V : ℕ}

/-- The register groups of a bounded literal header. In particular, every
address in the final column is local to the current printed descriptor. -/
@[ext] structure Fields (q t H N A w V : ℕ) where
  count : Fin (V+1)
  sizes : Fin V→Fin (H+1)×Fin (N+1)
  width : Fin V→Fin H→Fin (w+1)
  role : Fin V→Fin N→Fin (t+1)
  arity : Fin V→Fin N→Fin (A+1)
  operand : Fin V→Fin N→Fin A→Fin (q+H+1)

def fill (c : Control q t H N A w V) (v : Fin V) := DescentTerminalScalarHeader.extend c.2 (emptyBook q t H N A w) v
def atom (b : Book q t H N A w) (k : Fin N) := DescentTerminalScalarHeader.extend b.2.2.rows none k
def emit (c : Control q t H N A w V) : Fields q t H N A w V where
  count:=c.1
  sizes v:=((fill c v).1,(fill c v).2.1)
  width v:=DescentTerminalScalarHeader.extend (fill c v).2.2.width 0
  role v k:=((atom (fill c v) k).map fun z=>z.1.succ).getD 0
  arity v k:=((atom (fill c v) k).map fun z=>z.2.1).getD 0
  operand v k i:=((atom (fill c v) k).map fun z=>ref (Nat.le_of_lt_succ (fill c v).1.isLt) (z.2.2 i)).getD 0

def decode (f : Fields q t H N A w V) : Control q t H N A w V :=
  ⟨f.count,fun v=>
    let i:=v.castLE (Nat.le_of_lt_succ f.count.isLt)
    let hn:=f.sizes i
    ⟨hn.1,hn.2,⟨fun j=>f.width i (j.castLE (Nat.le_of_lt_succ hn.1.isLt)),
      fun k=>
        let z:=k.castLE (Nat.le_of_lt_succ hn.2.isLt)
        Fin.cases none (fun tag=>some (tag,f.arity i z,fun j=>readRef (f.operand i z j))) (f.role i z)⟩⟩⟩

private def readBookFields (b : Book q t H N A w) : Book q t H N A w :=
  ⟨b.1,b.2.1,⟨fun j=>DescentTerminalScalarHeader.extend b.2.2.width 0
    (j.castLE (Nat.le_of_lt_succ b.1.isLt)),fun k=>
      let row:=atom b (k.castLE (Nat.le_of_lt_succ b.2.1.isLt))
      Fin.cases none (fun tag=>some (tag,(row.map fun z=>z.2.1).getD 0,fun j=>
        readRef ((row.map fun z=>ref (Nat.le_of_lt_succ b.1.isLt) (z.2.2 j)).getD 0)))
        ((row.map fun z=>z.1.succ).getD 0)⟩⟩

private theorem readBookFields_eq (b : Book q t H N A w) : readBookFields b=b:=by
  rcases b with ⟨h,n,⟨width,rows⟩⟩
  simp only [readBookFields,atom,DescentTerminalScalarHeader.extend_castLE]
  apply congrArg (fun rs=>(⟨h,n,⟨width,rs⟩⟩:Book q t H N A w))
  funext k
  cases row : rows k with
  | none => simp []
  | some entry =>
    rcases entry with ⟨key,arity,refs⟩
    simp [ref_back]

theorem back (c : Control q t H N A w V) : decode (emit c)=c := by
  rcases c with ⟨n,books⟩
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change (fun v : Fin n.val=>readBookFields (fill (⟨n,books⟩:Control q t H N A w V)
    (v.castLE (Nat.le_of_lt_succ n.isLt))))=books
  funext v
  exact (congrArg readBookFields (DescentTerminalScalarHeader.extend_castLE books
    (emptyBook q t H N A w) (Nat.le_of_lt_succ n.isLt) v)).trans (readBookFields_eq (books v))

structure Six where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  f : ℕ

def capacity (q t H N A w V : ℕ) : Six :=
  ⟨V+1,((H+1)*(N+1))^V,((w+1)^H)^V,((t+1)^N)^V,((A+1)^N)^V,(((q+H+1)^A)^N)^V⟩

abbrev Digits (u : Six) := Fin u.a×Fin u.b×Fin u.c×Fin u.d×Fin u.e×Fin u.f
def Six.total (u : Six) := u.a*(u.b*(u.c*(u.d*(u.e*u.f))))

def serial (u : Six) : Digits u ≃ Fin u.total :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) (finProdFinEquiv : Fin u.e×Fin u.f≃Fin _)).trans finProdFinEquiv)).trans
      finProdFinEquiv)).trans finProdFinEquiv)).trans finProdFinEquiv

def digits (f : Fields q t H N A w V) : Digits (capacity q t H N A w V) :=
  (f.count,finFunctionFinEquiv (fun v=>finProdFinEquiv (f.sizes v)),
   finFunctionFinEquiv (fun v=>finFunctionFinEquiv (f.width v)),
   finFunctionFinEquiv (fun v=>finFunctionFinEquiv (f.role v)),
   finFunctionFinEquiv (fun v=>finFunctionFinEquiv (f.arity v)),
   finFunctionFinEquiv (fun v=>finFunctionFinEquiv (fun k=>finFunctionFinEquiv (f.operand v k))))

def unpack (z : Digits (capacity q t H N A w V)) : Fields q t H N A w V :=
  ⟨z.1,fun v=>finProdFinEquiv.symm (finFunctionFinEquiv.symm z.2.1 v),
   fun v=>finFunctionFinEquiv.symm (finFunctionFinEquiv.symm z.2.2.1 v),
   fun v=>finFunctionFinEquiv.symm (finFunctionFinEquiv.symm z.2.2.2.1 v),
   fun v=>finFunctionFinEquiv.symm (finFunctionFinEquiv.symm z.2.2.2.2.1 v),
   fun v k=>finFunctionFinEquiv.symm (finFunctionFinEquiv.symm (finFunctionFinEquiv.symm z.2.2.2.2.2 v) k)⟩

theorem unpack_digits (f : Fields q t H N A w V) : unpack (digits f)=f := by cases f; simp [unpack,digits]

def headerTable (q t H N A w V : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (capacity q t H N A w V).total=>
    (DescentTerminalScalarHeader.encode (decode (unpack ((serial _).symm i)))).val+1)

theorem table_actual (c : Control q t H N A w V) :
    let u:=capacity q t H N A w V
    (headerTable q t H N A w V)[((serial u) (digits (emit c))).val]'(by simpa only [headerTable,List.length_ofFn] using ((serial u) (digits (emit c))).isLt)=
      (DescentTerminalScalarHeader.encode c).val+1 := by
  intro u
  dsimp only [u]
  simp only [headerTable,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply,unpack_digits,back]

private theorem product {a b x y : ℕ} (one : a ≤ 2^x) (two : b ≤ 2^y) :
    a*b ≤ 2^(x+y) := by rw [pow_add]; exact Nat.mul_le_mul one two
private theorem power {a x : ℕ} (fit : a ≤ 2^x) (n : ℕ) : a^n ≤ 2^(n*x) := by
  simpa only [Nat.mul_comm n x,pow_mul] using Nat.pow_le_pow_left fit n

theorem table_room (q t H N A w V tagBits : ℕ) (tags : t ≤ 2^tagBits) :
    (capacity q t H N A w V).total ≤ 2^(rowBits q tagBits H N A w V) := by
  have leg (x : ℕ) : x ≤ 2^(lg x) := Nat.le_pow_clog (by decide) _
  have tr : t+1 ≤ 2^(tagBits+1) := by rw [pow_succ]; have:=Nat.two_pow_pos tagBits; omega
  have estimate:=product (leg (V+1)) (product (power (product (leg (H+1)) (leg (N+1))) V)
    (product (power (power (leg (w+1)) H) V) (product (power (power tr N) V)
      (product (power (power (leg (A+1)) N) V) (power (power (power (leg (q+H+1)) A) N) V)))))
  convert estimate using 2 <;> first | rfl | (simp only [rowBits,bookBits,nodeBits];ring)

/-- All six offset dictionaries plus the single shared format lookup. -/
theorem seven_tables (q t H N A w V tagBits : ℕ) (tags : t ≤ 2^tagBits) :
    let u:=capacity q t H N A w V
    u.a+u.b+u.c+u.d+u.e+u.f+u.total ≤ 7*2^(rowBits q tagBits H N A w V) := by
  intro u
  have ha : 0<u.a := by unfold u capacity; dsimp; positivity
  have hb : 0<u.b := by unfold u capacity; dsimp; positivity
  have hc : 0<u.c := by unfold u capacity; dsimp; positivity
  have hd : 0<u.d := by unfold u capacity; dsimp; positivity
  have he : 0<u.e := by unfold u capacity; dsimp; positivity
  have hf : 0<u.f := by unfold u capacity; dsimp; positivity
  have step (a b : ℕ) (ap : 0<a) (bp : 0<b) : a ≤ a*b ∧ b ≤ a*b :=
    ⟨Nat.le_mul_of_pos_right _ bp,Nat.le_mul_of_pos_left _ ap⟩
  have ef:=step _ _ he hf
  have defn:=step _ _ hd (Nat.mul_pos he hf)
  have cdef:=step _ _ hc (Nat.mul_pos hd (Nat.mul_pos he hf))
  have bcdef:=step _ _ hb (Nat.mul_pos hc (Nat.mul_pos hd (Nat.mul_pos he hf)))
  have all:=step _ _ ha (Nat.mul_pos hb (Nat.mul_pos hc (Nat.mul_pos hd (Nat.mul_pos he hf))))
  have top : u.total ≤ _ :=table_room q t H N A w V tagBits tags
  unfold Six.total at top ⊢
  omega

end
end Hierarchy.DescentTerminalPrintedFields

end OAI
