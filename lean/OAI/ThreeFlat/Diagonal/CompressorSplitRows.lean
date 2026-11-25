import OAI.ThreeFlat.Diagonal.CompressorGreedyColumns

namespace OAI
/-! # The native eight-way split of an old base displacement at a physical read address -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open RAM.DescriptorExpr
open private row_word from OAI.ThreeFlat.Diagonal.CompressorGreedyColumns
open scoped Fin.NatCast
variable {B H : Type} [AddCommGroup H] {w N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "C" => incoming S N p
local notation "x" => dims S N t l
local notation "f" => Template.f
local notation "o" => Template.o

omit [AddCommGroup H] in
theorem Old.splitStep (h : Old S P b p cell prior m) (pub : Fin 1→Word w) (u : B × Fin S.degree)
    (rev : Bool) (j : Fin 4) (splitEnd : p.split+8*(C).rows<2^w)
    (dim : S.degree<2^w ∧ 2^S.colors<2^w ∧ 2^t<2^w) (eight : 8<2^w) :
    let columnId:=(if rev then 4 else 0)+j.val
    let address:=p.split+(C).rows*columnId+SlotImage.ordinal b u
    (Template.emit cell (splitRow o Template.ptr (.reg 0) S.colors S.degree)).eval pub m
      (fun _=>(address:Word w)) =
      (StoredColumns.digit S.colors S.degree t j.val (m (SlotImage.cell C b u rev 2)).val:Word w) := by
  let col:=(if rev then 4 else 0)+j.val
  let ix:=SlotImage.ordinal b u
  let data:=SlotImage.cell C b u rev 2
  let addr:=p.split+(C).rows*col+ix
  let vs:=fun _ : Fin 1=>(addr:Word w)
  let V:=Formula.value (fun _=>cell) m vs
  let pos:=Formula.op .sub (.reg 0) (f splitShifts)
  let field:=Formula.op .div pos (f oldSlots)
  let row:=Formula.op .mod pos (f oldSlots)
  have hcol : col<8 := by cases rev <;> have := j.isLt <;> simp [col] <;> omega
  have hrow : ix<(C).rows := SlotImage.ordinal_lt b u
  have mul:=Nat.mul_le_mul_left (C).rows hcol
  rw [Nat.mul_succ] at mul
  have ins : (C).rows*col+ix<2^w := by omega
  have colFit : col<2^w := by omega
  have sr : V (f splitShifts)=(p.split:Word w) := h.header.field vs 16
  have gr : V (f oldGraph)=(p.oldGraph:Word w) := h.header.field vs 11
  have num : V (f oldSlots)=((C).rows:Word w) := h.header.field vs 12
  have tags : V (f ShrinkStage.tags)=((2^t:ℕ):Word w) := h.header.field vs 15
  have off : V pos=(((C).rows*col+ix:ℕ):Word w) := by
    change (addr:Word w)-V (f splitShifts)=_
    rw [sr];dsimp [addr];push_cast;abel
  have fieldVal : V field=(col:Word w) := by
    change BinaryOp.div.eval (V pos) (V (f oldSlots))=_
    rw [num,off,op_cast .div _ _ ⟨ins,by omega⟩]
    change ((((C).rows*col+ix)/(C).rows:ℕ):Word w)=_
    rw [Nat.mul_add_div (Nat.zero_lt_of_lt hrow),Nat.div_eq_of_lt hrow,Nat.add_zero]
  have rowVal : V row=(ix:Word w) := by
    change BinaryOp.mod.eval (V pos) (V (f oldSlots))=_
    rw [num,off,op_cast .mod _ _ ⟨ins,by omega⟩]
    change ((((C).rows*col+ix)%(C).rows:ℕ):Word w)=_
    simp [Nat.add_mod,Nat.mod_eq_of_lt hrow]
  let side:=Formula.op .div field (.lit 4)
  let kind:=Formula.op .mod field (.lit 4)
  have sideVal : V side=(col/4:ℕ) := by
    change BinaryOp.div.eval (V field) (4:Word w)=_
    rw [fieldVal,show (4:Word w)=((4:ℕ):Word w) from rfl,op_cast .div _ _ ⟨colFit,by omega⟩]
    rfl
  have kindVal : V kind=(j.val:Word w) := by
    change BinaryOp.mod.eval (V field) (4:Word w)=_
    rw [fieldVal,show (4:Word w)=((4:ℕ):Word w) from rfl,op_cast .mod _ _ ⟨colFit,by omega⟩]
    have rem : col % 4 = j.val := by
      have bound := j.isLt
      cases rev <;> dsimp [col] <;> omega
    exact congrArg (fun n : ℕ => (n : Word w)) rem
  let raw (col : ℕ):=Formula.load (.op .add (column o (f oldGraph) (f oldSlots) col) row)
  have rawVal : V (raw (SlotImage.column rev 2))=m data := by
    have cap : data < 2^w := (SlotImage.cell_range h.stored u rev 2).2.trans_le h.graphFits
    have addressWord : (p.oldGraph:Word w) + ((C).rows:Word w) *
        (SlotImage.column rev 2:Word w) + (ix:Word w) = (data:Word w) := by
      simpa only [data,SlotImage.cell,incoming,ix,Nat.add_assoc] using
        (row_word (w:=w) p.oldGraph (C).rows (SlotImage.column rev 2) ix)
    change m (V (f oldGraph)+V (f oldSlots)*((SlotImage.column rev 2):Word w)+V row).val=_
    rw [gr,num,rowVal,addressWord,Fin.val_cast_of_lt cap]
  let word:=Formula.select .eq side (.lit 0) (raw 2) (raw 5)
  have wordVal : V word=((m data).val:Word w) := by
    rw [Fin.cast_val_eq_self]
    change (if Comparison.eq.test (V side) (0:Word w) then V (raw 2) else V (raw 5))=_
    rw [sideVal]
    have one : (1:Word w)≠0 := by
      intro equal
      have q := congrArg Fin.val equal
      have ok : (1:Word w).val=1 := Fin.val_cast_of_lt (by omega : 1<2^w)
      rw [ok,Fin.val_zero] at q
      omega
    cases rev <;> fin_cases j <;> simp [col,Comparison.test,one] <;> exact rawVal
  let a:=(m data).val
  let lo:=Formula.op .div word (.lit (2^S.colors))
  let up:=Formula.op .div lo (.lit S.degree)
  have fitA : a<2^w := (m data).isLt
  have lowFit : a/2^S.colors<2^w := (Nat.div_le_self ..).trans_lt fitA
  have upFit : a/2^S.colors/S.degree<2^w := (Nat.div_le_self ..).trans_lt lowFit
  have lowVal : V lo=((a/2^S.colors:ℕ):Word w) := by
    change BinaryOp.div.eval (V word) ((2^S.colors:ℕ):Word w)=_
    rw [wordVal,op_cast .div _ _ ⟨fitA,dim.2.1⟩]; rfl
  have upVal : V up=((a/2^S.colors/S.degree:ℕ):Word w) := by
    change BinaryOp.div.eval (V lo) (S.degree:Word w)=_
    rw [lowVal,op_cast .div _ _ ⟨lowFit,dim.1⟩]; rfl
  change (Template.emit cell (splitRow o Template.ptr (.reg 0) S.colors S.degree)).eval pub m vs =
    (StoredColumns.digit S.colors S.degree t j.val a : Word w)
  rw [Template.program_value cell pub m vs]
  change V (.select .eq kind (.lit 0) (.op .mod word (.lit (2^S.colors)))
    (.select .eq kind (.lit 1) (.op .mod lo (.lit S.degree))
      (.select .eq kind (.lit 2) (.op .mod up (f ShrinkStage.tags)) (.op .div up (f ShrinkStage.tags)))))=_
  have choose (i : ℕ) (small : i < 4) (yes no : Formula 1) :
      V (.select .eq kind (.lit i) yes no) = if j.val=i then V yes else V no := by
    change (if Comparison.eq.test (V kind) (i:Word w) then V yes else V no) = _
    rw [kindVal,test_cast .eq _ _ (j.isLt.trans (by omega)) (small.trans (by omega))]
    by_cases eq : j.val = i <;> simp [natTest,eq]
  have mod0 : V (.op .mod word (.lit (2^S.colors)))=((a%2^S.colors:ℕ):Word w) := by
    change BinaryOp.mod.eval (V word) ((2^S.colors:ℕ):Word w)=_
    rw [wordVal,op_cast .mod _ _ ⟨fitA,dim.2.1⟩]; rfl
  have mod1 : V (.op .mod lo (.lit S.degree))=((a/2^S.colors%S.degree:ℕ):Word w) := by
    change BinaryOp.mod.eval (V lo) (S.degree:Word w)=_
    rw [lowVal,op_cast .mod _ _ ⟨lowFit,dim.1⟩]; rfl
  have mod2 : V (.op .mod up (f ShrinkStage.tags))=((a/2^S.colors/S.degree%2^t:ℕ):Word w) := by
    change BinaryOp.mod.eval (V up) (V (f ShrinkStage.tags))=_
    rw [upVal,tags,op_cast .mod _ _ ⟨upFit,dim.2.2⟩]; rfl
  have div3 : V (.op .div up (f ShrinkStage.tags))=((a/2^S.colors/S.degree/2^t:ℕ):Word w) := by
    change BinaryOp.div.eval (V up) (V (f ShrinkStage.tags))=_
    rw [upVal,tags,op_cast .div _ _ ⟨upFit,dim.2.2⟩]; rfl
  rw [choose 0 (by decide),choose 1 (by decide),choose 2 (by decide),mod0,mod1,mod2,div3]
  fin_cases j <;> rfl


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
