import OAI.ThreeFlat.RAM.HistoryStageBody
import OAI.ThreeFlat.RAM.HistoryStageChecked

namespace OAI
/-! # The physical addresses visited while emitting the six stage banks -/

namespace ThreeFlat.RAM.HistoryStageBounds

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr HistoryPartyBatchExec
open scoped Fin.CommRing
noncomputable section
variable {W : ℕ}

abbrev BankOutside (A : HistoryGatherBody.Layout) (cap : ℕ) (S : HistoryStageRoot.Input)
    (mem : Memory W) (b : HistoryStageRoot.Bank) (x : ℕ) :=
  x<HistoryStageBody.bankBase A cap S b ∨
    HistoryStageBody.bankBase A cap S b+HistoryStageBody.bankSize S (numeric mem) b≤x

def lastIncident (S : HistoryStageRoot.Input) (m : ℕ→ℕ) :=
  let h:=m (HistoryStageRoot.node S+6)
  m (h+1)+4*(m h-1)

/-- Source words of one real node, its kernel and its earlier children. The
last incident pair exists only for a nonempty incident directory. -/
structure BankCells (A : HistoryGatherBody.Layout) (cap : ℕ) (S : HistoryStageRoot.Input)
    (mem : Memory W) (b : HistoryStageRoot.Bank) : Prop where
  cursor : b=.result → Cell W (BankOutside A cap S mem b) A.nodePorts.cursor
  args : ∀ j : Fin 11, Cell W (BankOutside A cap S mem b) (HistoryStageBody.args A+j.val)
  node : ∀ j : Fin 8, Cell W (BankOutside A cap S mem b) (HistoryStageRoot.node S+j.val)
  child : ∀ i, i<HistoryStageRoot.childCount S (numeric mem) →
    Cell W (BankOutside A cap S mem b) (numeric mem (HistoryStageRoot.node S+3)+i)
  kernel : ∀ j : Fin 6, Cell W (BankOutside A cap S mem b) (S.kernel+j.val)
  old : ∀ i, i<HistoryStageRoot.childCount S (numeric mem) → ∀ j : Fin 6,
    Cell W (BankOutside A cap S mem b) (HistoryStageRoot.childPtr S (numeric mem) i+j.val)
  incident : ∀ j : Fin 2, Cell W (BankOutside A cap S mem b) (numeric mem (HistoryStageRoot.node S+6)+j.val)
  last : 0<numeric mem (numeric mem (HistoryStageRoot.node S+6)) →
    ∀ j, 2≤j → j≤3 → Cell W (BankOutside A cap S mem b) (lastIncident S (numeric mem)+j)

section Formula
variable {m : ℕ→ℕ} {vs : Fin 13→ℕ} {ok : ℕ→Prop}
local notation "Test" => Checked W ok m vs
local notation "V" => value W m vs

private theorem checkAdd {x y : Formula 13} (hx : Test x) (hy : Test y) : Test (add x y) :=
  ⟨hx,hy,trivial⟩
private theorem checkMul {x y : Formula 13} (hx : Test x) (hy : Test y) : Test (mul x y) :=
  ⟨hx,hy,trivial⟩
private theorem checkRead {x : Formula 13} (hx : Test x) (j : ℕ) (safe : Cell W ok (V x+j)) :
    Test (HistoryStageRoot.read x j) := ⟨checkAdd hx trivial,safe⟩

private theorem checkField {x : Formula 13} (xs : List (Formula 13)) (hx : Test x)
    (bound : V x<2^W) (one : 1<2^W) (all : ∀ a∈xs,Test a) : Test (HistoryStageRoot.field x xs) := by
  induction xs generalizing x with
  | nil => trivial
  | cons a rest ih =>
    have cut : Test (sub x (.lit 1)) := ⟨hx,trivial,bound,one⟩
    refine ⟨hx,trivial,bound,by exact Nat.two_pow_pos _,all a (by simp),?_⟩
    exact ih cut ((Nat.sub_le ..).trans_lt bound) (fun e he=>all e (by simp [he]))

/-- Every native load in a prefix step uses a selected list entry or falls back
to the resident argument and kernel records, including the eager false arm. -/
private theorem checkPrefix {top : Formula 13} {j cap k : ℕ}
    (topOk : Test top) (topWord : V top<2^W)
    (capWord : cap<2^W) (hk : k≤cap) (fieldNum : j≤6)
    (argTwo : Test (HistoryStageRoot.arg 2)) (argThree : Test (HistoryStageRoot.arg 3))
    (array : Test (HistoryStageRoot.nd 3)) (base : Cell W ok (vs 0))
    (words : ∀ p,m p<2^W)
    (list : ∀ i,i<V top → Cell W ok (V (HistoryStageRoot.nd 3)+i))
    (rows : ∀ i,i<V top → ∀ f : Fin 6,Cell W ok (V (HistoryStageRoot.child (.lit i))+f.val))
    (kernel : ∀ f : Fin 6, Cell W ok (V (HistoryStageRoot.arg 3)+f.val)) :
    Test (HistoryStageRoot.sum top j k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have kw : k<2^W:=lt_of_lt_of_le (by omega : k<cap) capWord.le
    let slot : Formula 13 := lt (.lit k) top (add (HistoryStageRoot.nd 3) (.lit k)) (.reg 0)
    have sel : Test slot:=⟨trivial,topOk,kw,topWord,checkAdd array trivial,trivial⟩
    have addr : Cell W ok (V slot) := by
      by_cases h : k<V top
      · simpa [slot,value,lt,Formula.natural,natOp,natTest,h] using list k h
      · simpa [slot,value,lt,Formula.natural,natOp,natTest,h] using base
    have ptr : Test (HistoryStageRoot.prefixChild k top) := by
      exact ⟨trivial,topOk,kw,topWord,checkAdd argTwo (checkMul trivial (show Test (.load slot) from ⟨sel,addr⟩)),argThree⟩
    have inspect (f : Fin 6) : Test (HistoryStageRoot.read (HistoryStageRoot.prefixChild k top) f.val) := by
      apply checkRead ptr
      by_cases h : k<V top
      · simpa [HistoryStageRoot.prefixChild,HistoryStageRoot.child,value,Formula.natural,lt,add,mul,natOp,natTest,h] using rows k h f
      · simpa [HistoryStageRoot.prefixChild,value,Formula.natural,lt,natTest,h] using kernel f
    have data : Test (HistoryStageRoot.info (HistoryStageRoot.prefixChild k top) j) := by
      unfold HistoryStageRoot.info
      split
      · exact ⟨inspect 1,inspect 5,words _,words _⟩
      · exact inspect ⟨j,by omega⟩
    exact checkAdd (ih (by omega)) ⟨trivial,topOk,kw,topWord,data,trivial⟩

end Formula

open HistoryStageBody HistoryStageRoot
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem bank_checked (A : HistoryGatherBody.Layout) (cap : ℕ) (S : Input)
    (mem : Memory W) (b : Bank)
    (header : ∀ f : Fin 11,numeric mem (args A+f.val)=S.words f)
    (space : bankBase A cap S b+bankSize S (numeric mem) b<2^W)
    (children : childCount S (numeric mem)≤cap) (capFit : cap<2^W) (wide : 11<2^W)
    (slots : BankCells A cap S mem b)
    (i : Fin (rowCount (childCount S (numeric mem)) b)) (j : Fin b.width) :
    Checked W (BankOutside A cap S mem b) (numeric mem) (regs (args A) (b.width*i.val+j.val))
      (formula cap b) := by
  let raw:=numeric mem
  let cn:=childCount S raw
  let key:=b.width*i.val+j.val
  let vs:=regs (args A) key
  let V:=value W raw vs
  let good:=Checked W (BankOutside A cap S mem b) raw vs
  let cell:=Cell W (BankOutside A cap S mem b)
  change good (formula cap b)
  have reg0 : vs 0=args A := by simp [vs,regs]
  have reg5 : vs 5=key := by simp [vs,regs]
  have rowBound (n : ℕ) (bank : Bank) : rowCount n bank≤n+1 := by
    cases bank <;> simp only [rowCount] <;> omega
  have iBound : i.val≤cn := Nat.le_of_lt_succ (i.isLt.trans_le (rowBound cn b))
  have nonzero : 0<b.width := by cases b <;> decide
  have widthFit : b.width<2^W := by cases b <;> simp only [Bank.width] <;> omega
  have keyFit : key<2^W := by
    have r:=Nat.mul_le_mul_left b.width (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at r
    have h:=j.isLt
    dsimp [key]
    unfold bankSize at space
    omega
  have words (x : ℕ) : raw x<2^W:=(mem x).isLt
  let idx : Formula 13:=div (.reg 5) (.lit b.width)
  let col : Formula 13:=rem (.reg 5) (.lit b.width)
  let z:=sub idx (.lit 1)
  have indexV : V idx=i.val := by
    change vs 5/b.width=i.val
    rw [reg5,show key=b.width*i.val+j.val from rfl,Nat.mul_add_div nonzero,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have colV : V col=j.val := by
    change vs 5%b.width=j.val
    rw [reg5,show key=b.width*i.val+j.val from rfl,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  have zV : V z=i.val-1 := by change V idx-1=_;rw [indexV]
  have indexFit : V idx<2^W := by rw [indexV];exact (iBound.trans children).trans_lt capFit
  have zFit : V z<2^W:=by rw [zV];omega
  have colFit : V col<2^W:=by rw [colV];exact j.isLt.trans widthFit
  have indexGood : good idx:=⟨trivial,trivial,(by change vs 5<_;rw [reg5];exact keyFit),widthFit⟩
  have colGood : good col:=⟨trivial,trivial,(by change vs 5<_;rw [reg5];exact keyFit),widthFit⟩
  have one : 1<2^W:=by omega
  have zGood : good z:=⟨indexGood,trivial,indexFit,one⟩
  have av (f : Fin 11) : V (arg f.val)=S.words f := by
    change raw (vs 0+f.val)=_
    rw [reg0];exact header f
  have ag (f : Fin 11) : good (arg f.val) := by
    refine ⟨checkAdd trivial trivial,?_⟩
    change cell (vs 0+f.val);rw [reg0];exact slots.args f
  have a0 : V (arg 0)=S.id:=av 0
  have a1 : V (arg 1)=S.nodeBase:=av 1
  have a2 : V (arg 2)=S.resultBase:=av 2
  have a3 : V (arg 3)=S.kernel:=av 3
  have ndBase : good (add (arg 1) (mul (.lit 8) (arg 0))) :=
    checkAdd (ag 1) (checkMul trivial (ag 0))
  have nodeBase : V (add (arg 1) (mul (.lit 8) (arg 0)))=node S := by
    change V (arg 1)+8*V (arg 0)=_
    rw [a1,a0];rfl
  have ng (f : Fin 8) : good (nd f.val) := by
    apply checkRead ndBase
    change cell (V (add (arg 1) (mul (.lit 8) (arg 0)))+f.val)
    rw [nodeBase];exact slots.node f
  have nv (f : ℕ) : V (nd f)=raw (node S+f) := by
    change raw (V (add (arg 1) (mul (.lit 8) (arg 0)))+f)=_;rw [nodeBase]
  have C : V (nd 4)=cn:=nv 4
  have arr (p : ℕ) : V (child (.lit p))=childPtr S raw p := by
    change V (arg 2)+8*raw (V (nd 3)+p)=_
    rw [a2,nv];rfl
  have baseCell : cell (vs 0) := by simpa [reg0] using slots.args (0:Fin 11)
  have kernels (f : Fin 6) : cell (V (arg 3)+f.val):=by rw [a3];exact slots.kernel f
  have prefixOk (top : Formula 13) (tg : good top) (tw : V top<2^W) (tc : V top≤cn)
      (f : ℕ) (hf : f≤6) : good (HistoryStageRoot.sum top f cap) := by
    apply checkPrefix tg tw capFit le_rfl hf (ag 2) (ag 3) (ng 3) baseCell words
    · intro k hk
      change cell (V (nd 3)+k)
      rw [nv];exact slots.child k (hk.trans_le tc)
    · intro k hk q
      change cell (V (child (.lit k))+q.val)
      rw [arr];exact slots.old k (hk.trans_le tc) q
    · exact kernels
  have oldGood := prefixOk (nd 4) (ng 4) (by rw [C];exact children.trans_lt capFit) C.le 6 le_rfl
  have zero : 0<2^W:=Nat.two_pow_pos _
  have chooseZero {x y : Formula 13} (hx : good x) (hy : good y) :
      good (eqz idx (.lit 0) x y) := ⟨indexGood,trivial,indexFit,zero,hx,hy⟩
  let addr:=eqz idx (.lit 0) (.reg 0) (add (nd 3) z)
  let src:=eqz idx (.lit 0) (arg 3) (add (arg 2) (mul (.lit 8) (.load addr)))
  have addrV : V addr=if V idx=0 then vs 0 else V (nd 3)+V z := by
    change (if decide (V idx=0)=true then vs 0 else V (nd 3)+V z)=_
    by_cases h : V idx=0 <;> simp [h]
  have srcV : V src=if V idx=0 then V (arg 3) else V (arg 2)+8*raw (V addr) := by
    change (if decide (V idx=0)=true then V (arg 3) else V (arg 2)+8*raw (V addr))=_
    by_cases h : V idx=0 <;> simp [h]
  have addrOk : good addr:=chooseZero trivial (checkAdd (ng 3) zGood)
  have addrCell : cell (V addr) := by
    rw [addrV,indexV,zV,nv]
    split
    · exact baseCell
    · exact slots.child (i.val-1) (show i.val-1<cn by omega)
  have srcOk : good src := chooseZero (ag 3) (checkAdd (ag 2) (checkMul trivial ⟨addrOk,addrCell⟩))
  have srcRead (f : Fin 6) : good (HistoryStageRoot.read src f.val) := by
    apply checkRead srcOk
    change cell (V src+f.val)
    rw [srcV,indexV,a3,a2]
    by_cases h : i.val=0
    · rw [ite_eq_left h];exact slots.kernel f
    · rw [ite_eq_right h]
      have live : V addr=raw (node S+3)+(i.val-1) := by
        rw [addrV,indexV,ite_eq_right h,nv,zV]
      rw [live];exact slots.old (i.val-1) (show i.val-1<cn by omega) f
  let count : Formula 13:=.load (nd 6)
  let last:=eqz count (.lit 0) (.reg 0)
    (add (HistoryStageRoot.read (nd 6) 1) (mul (.lit 4) (sub count (.lit 1))))
  let width:=eqz count (.lit 0) (.lit 0) (add (HistoryStageRoot.read last 3) (HistoryStageRoot.read last 2))
  let all:=add (nd 7) width
  have countAt : V count=raw (raw (node S+6)) := by change raw (V (nd 6))=_;rw [nv]
  have countFit : V count<2^W:=words _
  have countOk : good count := by
    refine ⟨ng 6,?_⟩
    change cell (V (nd 6))
    rw [nv 6]
    simpa using slots.incident 0
  have head1 : good (HistoryStageRoot.read (nd 6) 1) := by
    apply checkRead (ng 6)
    change cell (V (nd 6)+1)
    rw [nv 6]
    exact slots.incident 1
  have lastOk : good last :=
    ⟨countOk,trivial,countFit,zero,trivial,checkAdd head1 (checkMul trivial ⟨countOk,trivial,countFit,one⟩)⟩
  have lastV : V last=if V count=0 then vs 0 else raw (V (nd 6)+1)+4*(V count-1) := by
    change (if decide (V count=0)=true then vs 0 else raw (V (nd 6)+1)+4*(V count-1))=_
    by_cases empty : V count=0 <;> simp [empty]
  have component (f : ℕ) (lo : 2≤f) (hi : f≤3) : good (HistoryStageRoot.read last f) := by
    apply checkRead lastOk
    change cell (V last+f)
    rw [lastV,countAt,nv 6]
    split
    · rw [reg0];exact slots.args ⟨f,by omega⟩
    · rename_i nonempty
      have positive : 0 < raw (raw (node S+6)) := Nat.pos_of_ne_zero nonempty
      exact slots.last positive f lo hi
  have allOk : good all := checkAdd (ng 7)
    ⟨countOk,trivial,countFit,zero,trivial,checkAdd (component 3 (by decide) le_rfl) (component 2 le_rfl (by decide))⟩
  have prefixZ (f : ℕ) (hf : f≤6) := prefixOk z zGood zFit (by rw [zV];omega) f hf
  have prefixI (f : ℕ) (hf : f≤6) := prefixOk idx indexGood indexFit (by rw [indexV];exact iBound) f hf
  have prefixC (f : ℕ) (hf : f≤6) := prefixOk (nd 4) (ng 4) (by rw [C];exact children.trans_lt capFit) C.le f hf
  have kr (f : Fin 6) : good (HistoryStageRoot.read (arg 3) f.val) := checkRead (ag 3) _ (kernels f)
  have pinMap := chooseZero (ag 5) (checkAdd (checkAdd (ag 5) (kr 1)) (prefixZ 1 (by decide)))
  have dest := checkAdd (ag 7) (prefixI 5 (by decide))
  have childAt (lt : i.val<cn) (f : Fin 6) : good (HistoryStageRoot.read (child idx) f.val) := by
    have loc : cell (V (nd 3)+V idx) := by rw [nv,indexV];exact slots.child _ lt
    have cg : good (child idx) := checkAdd (ag 2) (checkMul trivial ⟨checkAdd (ng 3) indexGood,loc⟩)
    apply checkRead cg
    change cell (V (arg 2)+8*raw (V (nd 3)+V idx)+f.val)
    rw [a2,nv,indexV];exact slots.old _ lt f
  have entries (xs : List (Formula 13)) (g : ∀ e∈xs,good e) :
      good (HistoryStageRoot.field col xs) := checkField xs colGood colFit one g
  have litGood (n : ℕ) : good (.lit n) := trivial
  have nilGood : ∀ x ∈ ([] : List (Formula 13)), good x := by simp
  cases b with
  | hub =>
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨ag 4,allOk,oldGood,checkAdd (ng 4) (litGood 1),ag 8,ag 9,nilGood⟩
  | link =>
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨srcOk,pinMap,litGood 8,checkAdd (ag 6) (checkMul (litGood 5) indexGood),nilGood⟩
  | mapArgs =>
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨pinMap,srcRead 1,chooseZero oldGood (srcRead 5),
      checkAdd (litGood 2) (chooseZero allOk (prefixZ 5 (by decide))),
      checkAdd (litGood 2) (chooseZero (ng 7) (checkAdd allOk (prefixZ 6 le_rfl))),nilGood⟩
  | result =>
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨ag 4,allOk,checkAdd (kr 2) (prefixC 2 (by decide)),
      checkAdd (checkAdd oldGood (kr 3)) (prefixC 3 (by decide)),ag 7,ng 7,nilGood⟩
  | extArgs =>
    have lt : i.val<cn:=i.isLt
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨dest,childAt lt 5,childAt lt 4,nilGood⟩
  | extCommand =>
    have lt : i.val<cn:=i.isLt
    apply entries
    simp only [List.forall_mem_cons]
    exact ⟨checkAdd (ag 10) (checkMul (litGood 3) indexGood),dest,litGood 10,litGood 0,litGood 0,litGood 0,
      checkAdd dest (childAt lt 5),nilGood⟩


end
end ThreeFlat.RAM.HistoryStageBounds

end OAI
