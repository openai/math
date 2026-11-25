import OAI.Hierarchy.GridIdleGuard
import OAI.Hierarchy.GridSelfHeader
import OAI.Hierarchy.GridIdleLayout
import OAI.Hierarchy.GridOrderedSources
import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Native publication of the identity controller's rail map and literal inputs -/

namespace Hierarchy.GridControllerIdle
open ThreeFlat RAM Diagonal RAM.PhysicalPinsExpr RAM.PhysicalProcedure
open RAM.DescriptorScan Computability.VPVNP.BurstRAM PrivateRAM UniversalGrid GridThrough GridThrough.Ordered
open scoped Fin.CommRing
noncomputable section

/-- Uniform public lengths; a cell has `q` ticks, each with `pins` incoming bits. -/
structure Shape where
  axes : ℕ
  radix : ℕ
  railsPer : ℕ
  twoB : ℕ
  logRadix : ℕ
  q : ℕ
  pins : ℕ
  pc : ℕ

def Shape.rails (b : Shape) := b.axes*b.railsPer

def Shape.data (b : Shape) := b.radix^b.axes*(b.q*b.pins)

inductive Column where | direction | cell | powers | touch | data
  deriving DecidableEq

def base (A : GridOrderedSources.Arena) : Column → ℕ
  | .direction => A.railMap.dir | .cell => A.railMap.cell | .powers => A.railMap.powers
  | .touch => A.railMap.touch | .data => A.pins.data

def count (b : Shape) : Column → ℕ
  | .direction | .cell | .touch => b.rails | .powers => b.axes | .data => b.data

private abbrev X := Formula 1
private abbrev lit (a : ℕ) : X := .lit a
private abbrev bin (op : BinaryOp) (x y : X) : X := .op op x y
private abbrev divBy (x : X) (y : ℕ) : X := bin .div x (lit y)
private abbrev modBy (x : X) (y : ℕ) : X := bin .mod x (lit y)
private abbrev power (b : Shape) (j : X) : X := bin .shiftLeft (lit 1) (bin .mul (lit b.logRadix) j)

/-- All instruction words of the accepting program are zero except the first
word of each instruction, whose tag is 13. ProgramBits uses low bits first. -/
def literalWord (W pins pc i : ℕ) : ℕ :=
  let j := i%pins/W
  if 0 < j ∧ j ≤ 6*pc ∧ (j-1)%6=0 then (13 >>> (i%pins%W))%2 else 0

private def acceptWord (W : ℕ) (b : Shape) (row : X) : X :=
  let a := modBy row b.pins
  let j := divBy a W
  .select .eq j (lit 0) (lit 0) (.select .lt (lit (6*b.pc)) j (lit 0)
    (.select .eq (modBy (.cut j (lit 1)) 6) (lit 0)
      (modBy (bin .shiftRight (lit 13) (modBy a W)) 2) (lit 0)))

/-- Each output is written at its own absolute address. The formulas have
fixed syntax and use only the public shape and the running address. -/
def expr (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (col : Column) : X :=
  let i := Formula.cut (.reg 0) (lit (base A col))
  let d := divBy i b.railsPer
  let z := divBy (modBy i b.railsPer) b.twoB
  let p := power b d
  match col with
  | .direction => d
  | .cell => bin .add (bin .mod z p) (bin .mul (bin .div z p) (bin .mul p (lit b.radix)))
  | .powers => power b i
  | .touch => lit b.radix
  | .data => acceptWord W b i

/-- Numeric contents of each installed bank, indexed from its own base. -/
def word (W : ℕ) (b : Shape) (i : ℕ) : Column → ℕ
  | .direction => i/b.railsPer
  | .cell =>
    let d := i/b.railsPer
    let z := i%b.railsPer/b.twoB
    let p := b.radix^d
    z%p+(z/p)*(p*b.radix)
  | .powers => b.radix^i
  | .touch => b.radix
  | .data => literalWord W b.pins b.pc i

/-- Only the public scalar geometry enters the elementary word range check. -/
structure Fits (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) : Prop where
  stop : ∀ col, base A col+count b col < 2^W
  radix : b.radix=2^b.logRadix
  scale : b.logRadix*b.axes < W
  per : 0 < b.railsPer
  scalar : b.railsPer < 2^W ∧ b.twoB < 2^W ∧ b.pins < 2^W ∧ 6*b.pc < 2^W ∧ W < 2^W ∧ 13 < 2^W
  width : 0 < W

private theorem power_nat {W : ℕ} (b : Shape) (j : ℕ) (eqn : b.radix=2^b.logRadix)
    (h : b.logRadix*j < W) : natOp W .shiftLeft 1 (b.logRadix*j)=b.radix^j := by
  rw [eqn,←pow_mul]; simp [natOp,h,Nat.shiftLeft_eq]

private theorem accept_nat (W : ℕ) (b : Shape) (i : ℕ) (width : 0 < W) :
    (acceptWord W b (.lit i)).natural W (fun _=>0) (fun _=>0) (fun _=>0)=
      literalWord W b.pins b.pc i := by
  let index := i%b.pins/W
  have shift := Nat.mod_lt (i%b.pins) width
  by_cases zero : index=0
  · simp [acceptWord,modBy,divBy,lit,bin,Formula.natural,natTest,natOp,literalWord,
      ←show index=i%b.pins/W from rfl,zero]
  · have pos := Nat.pos_of_ne_zero zero
    by_cases beyond : 6*b.pc < index
    · have out := Nat.not_le_of_gt beyond
      simp [acceptWord,modBy,divBy,lit,bin,Formula.natural,natTest,natOp,literalWord,
        ←show index=i%b.pins/W from rfl,zero,pos,beyond,out]
    · have inside := Nat.le_of_not_gt beyond
      by_cases tag : (index-1)%6=0 <;>
        simp [acceptWord,modBy,divBy,lit,bin,Formula.natural,natTest,natOp,literalWord,
          ←show index=i%b.pins/W from rfl,zero,pos,beyond,inside,tag,shift]

private theorem expr_word {W : ℕ} {A : GridOrderedSources.Arena} {b : Shape} (fit : Fits W A b)
    (c : Column) (a : Word W) (o : Memory W) (lo : base A c ≤ a.val) (hi : a.val < base A c+count b c) :
    (expr W A b c).value (fun _=>0) o (fun _=>a)=(word W b (a.val-base A c) c : Word W) := by
  let i := a.val-base A c
  have ie : a.val-base A c=i := rfl
  have ix : i < count b c := by dsimp [i]; omega
  have aw := a.isLt
  have basew : base A c < 2^W := lt_of_le_of_lt (Nat.le_add_right ..) (fit.stop c)
  have iw : i < 2^W := lt_of_le_of_lt (Nat.sub_le ..) aw
  obtain ⟨per,two,pins,pc,Wsmall,tag⟩ := fit.scalar
  have one : 1 < 2^W := by omega
  have six : 6 < 2^W := by omega
  have two' : 2 < 2^W := by omega
  have hrad := fit.radix
  have fill (h : (expr W A b c).Fits W (fun _=>0) (fun x=>(o x).val) (fun _=>a.val)) :=
    (expr W A b c).value_eq_natural (w:=W) (fun _=>0) (fun x=>(o x).val) (fun _=>a.val) h
  have adiv : i/b.railsPer ≤ i := Nat.div_le_self ..
  have zbound : i%b.railsPer/b.twoB < 2^W := lt_of_le_of_lt (Nat.div_le_self ..)
    (lt_of_le_of_lt (Nat.mod_le ..) iw)
  have value (hf : (expr W A b c).Fits W (fun _=>0) (fun x=>(o x).val) (fun _=>a.val)) :
      (expr W A b c).value (fun _=>0) o (fun _=>a)=
        ((expr W A b c).natural W (fun _=>0) (fun x=>(o x).val) (fun _=>a.val) : Word W) := by
    simpa only [Nat.cast_zero,Fin.cast_val_eq_self] using fill hf
  cases c with
  | direction =>
    apply value
    simp [expr,Formula.Fits,Formula.natural,opFits,aw,basew,per,ie,iw]
  | cell =>
    have d : i/b.railsPer < b.axes := (Nat.div_lt_iff_lt_mul fit.per).2 (by simpa [count,Shape.rails] using ix)
    have exp : b.logRadix*(i/b.railsPer) < W := lt_of_le_of_lt (Nat.mul_le_mul_left _ d.le) fit.scale
    have val := power_nat b (i/b.railsPer) hrad exp
    have pwo : b.radix^(i/b.railsPer) < 2^W := by rw [hrad,←pow_mul]; exact Nat.pow_lt_pow_right (by decide) exp
    have sf : (expr W A b .cell).Fits W (fun _=>0) (fun x=>(o x).val) (fun _=>a.val) := by
      simp only [expr,divBy,modBy,power,bin,lit,Formula.Fits,Formula.natural,opFits]
      simp only [show ∀x y, natOp W .div x y=x/y from fun _ _=>rfl,
        show ∀x y, natOp W .mod x y=x%y from fun _ _=>rfl,
        show ∀x y, natOp W .mul x y=x*y from fun _ _=>rfl,ie,val]
      simp [one,per,two,aw,basew,iw,pwo,zbound,
        lt_trans exp Wsmall,lt_of_le_of_lt (Nat.mod_le i _) iw]
    rw [value sf]
    simp only [expr,word,power,divBy,modBy,bin,lit,Formula.natural,ie,
      show ∀x y, natOp W .add x y=x+y from fun _ _=>rfl,
      show ∀x y, natOp W .mod x y=x%y from fun _ _=>rfl,
      show ∀x y, natOp W .div x y=x/y from fun _ _=>rfl,
      show ∀x y, natOp W .mul x y=x*y from fun _ _=>rfl,val]
  | powers =>
    have d : i < b.axes := ix
    have exp : b.logRadix*i < W := lt_of_le_of_lt (Nat.mul_le_mul_left _ d.le) fit.scale
    have val := power_nat b i hrad exp
    rw [value (by simp [expr,power,lit,bin,Formula.Fits,Formula.natural,opFits,natOp,ie,
      one,aw,basew,lt_trans exp Wsmall])]
    exact congrArg (fun t : ℕ => (t:Word W)) val
  | touch => rfl
  | data =>
    have bitlt := Nat.mod_lt (i%b.pins) fit.width
    have pm : i%b.pins < 2^W := lt_of_le_of_lt (Nat.mod_le ..) iw
    have qw : i%b.pins/W < 2^W := lt_of_le_of_lt (Nat.div_le_self ..) pm
    have bitw := lt_trans bitlt Wsmall
    have shift : 13>>>(i%b.pins%W) < 2^W := lt_of_le_of_lt (Nat.shiftRight_le ..) tag
    have jm : (i%b.pins/W-1)%6 < 2^W := lt_of_le_of_lt (Nat.mod_le ..) (lt_of_le_of_lt (Nat.sub_le ..) qw)
    have hh : (expr W A b .data).Fits W (fun _=>0) (fun x=>(o x).val) (fun _=>a.val) := by
      simp [expr,acceptWord,Formula.Fits,Formula.natural,opFits,natOp,natTest,ie,
        aw,basew,iw,pm,qw,pins,Wsmall,one,six,two',pc,tag,bitlt,bitw,shift,jm,
        lt_of_le_of_lt (Nat.sub_le (i%b.pins/W) 1) qw]
    rw [value hh]
    exact congrArg (fun t : ℕ => (t : Word W)) (accept_nat W b i fit.width)

def scan (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (col : Column) : Procedure W :=
  PhysicalInputPhases.writing (HeaderScan.closed (expr W A b col)) Fin.elim0 (base A col) (count b col)

def fee (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (col : Column) :=
  4+count b col*(2*(expr W A b col).work+4)

def update {W : ℕ} (A : GridOrderedSources.Arena) (b : Shape) (col : Column) (m : Memory W) :=
  fillSegment (base A col) (count b col) (fun a => (word W b (a-base A col) col : Word W)) m

theorem scan_run {W : ℕ} {A : GridOrderedSources.Arena} {b : Shape} (fit : Fits W A b)
    (col : Column) (m : Memory W) : (scan W A b col).Exec m (update A b col m) (fee W A b col) := by
  unfold scan fee update
  rw [←HeaderScan.binds_closed (w:=W) (expr W A b col)]
  intro labels registers slots machine pc reg pub exit rom data cfg input start same
  subst input
  refine PhysicalInputPhases.writing_spec (HeaderScan.closed (expr W A b col)) Fin.elim0
    (base A col) (count b col) (fit.stop col) (·=m)
    (fun a => (word W b (a-base A col) col : Word W)) ?_
    machine pc reg pub exit rom data cfg m start rfl
  rintro _ rfl a o lo hi _
  rw [HeaderScan.eval_closed]; exact expr_word fit col a o lo hi

def procedure (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) : Procedure W :=
  let f := scan W A b
  ((((f .direction).seq (f .cell)).seq (f .powers)).seq (f .touch)).seq (f .data)

def cost (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) :=
  let f := fee W A b
  f .direction+f .cell+f .powers+f .touch+f .data

def image {W : ℕ} (A : GridOrderedSources.Arena) (b : Shape) (m : Memory W) :=
  let f := update (W:=W) A b
  f .data (f .touch (f .powers (f .cell (f .direction m))))

theorem exec {W : ℕ} {A : GridOrderedSources.Arena} {b : Shape} (fit : Fits W A b) (m : Memory W) :
    (procedure W A b).Exec m (image A b m) (cost W A b) := by
  intro labels registers slots machine
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
    (scan_run fit .direction m) (scan_run fit .cell _)) (scan_run fit .powers _))
    (scan_run fit .touch _)) (scan_run fit .data _) machine

structure Room (A : GridOrderedSources.Arena) (b : Shape) : Prop where
  rails : b.rails ≤ A.J/8
  axes : b.axes ≤ A.J/8
  data : b.data ≤ A.J

private theorem distinct_ranges {A : GridOrderedSources.Arena} {b : Shape} (room : Room A b)
    (c d : Column) (h : c≠d) (i : ℕ) (ih : i < count b c) :
    ¬ (base A d ≤ base A c+i ∧ base A c+i < base A d+count b d) := by
  obtain ⟨rails,axes,data⟩ := room
  cases c <;> cases d <;> simp_all [base,count,GridOrderedSources.Arena.pins,GridOrderedSources.Arena.railMap] <;> omega

private theorem image_at {W : ℕ} {A : GridOrderedSources.Arena} {b : Shape} (room : Room A b)
    (c : Column) (i : ℕ) (ih : i < count b c) (m : Memory W) :
    image A b m (base A c+i)=(word W b i c : Word W) := by
  have off (d : Column) (h : c≠d) := distinct_ranges room c d h i ih
  have at_ : base A c ≤ base A c+i ∧ base A c+i < base A c+count b c := ⟨by omega,by omega⟩
  cases c <;> simp [image,update,fillSegment,at_,fun d h => off d h]

private theorem image_low {W : ℕ} (A : GridOrderedSources.Arena) (b : Shape) (m : Memory W)
    (a : ℕ) (h : a < 5*A.J) : image A b m a=m a := by
  have off (c : Column) : ¬base A c ≤ a := by
    cases c <;> dsimp [base,GridOrderedSources.Arena.railMap,GridOrderedSources.Arena.pins] <;> omega
  simp [image,update,fillSegment,off]

/-- The canonical opcode rule, including the all-zero header, unused operand
words, and the program's public constants. -/
private theorem accept_words (W pc r K : ℕ) (hp : 0 < pc) (j : ℕ) :
    programWords (UniversalTick.accept W pc r K hp) j=
      ((if 0 < j ∧ j ≤ 6*pc ∧ (j-1)%6=0 then 13 else 0 : ℕ) : Word W) := by
  cases j with
  | zero => simp [programWords,UniversalTick.accept]
  | succ j =>
    have cut : j/6 < pc ↔ j+1 ≤ 6*pc := by omega
    simp only [programWords,UniversalTick.accept,instructionRow,Nat.zero_lt_succ,true_and,
      Nat.add_sub_cancel]
    by_cases h : j/6 < pc
    · rw [dite_eq_left h]; simp only [cut.mp h,true_and]; dsimp
      have tag (u : Fin 6) : (⟨13,0,0,0,0,0⟩ : InstructionRow).get u =
          (if u.val=0 then 13 else 0) := by
        fin_cases u <;> rfl
      exact congrArg (fun v : ℕ => (v : Word W)) (tag ⟨j%6,Nat.mod_lt _ (by decide)⟩)
    · rw [dite_eq_right h]; split <;> simp [show ¬j+1 ≤ 6*pc from fun hh => h (cut.mpr hh)]

private theorem accept_at {w pc r K q S : ℕ} (hp : 0 < pc) (hw : 13 < 2^(64*w))
    (i : Fin (q*S)) : (GridIdleLayout.literal (w:=w) (r:=r) (K:=K) hp i).toNat=
      literalWord (64*w) S pc i.val := by
  let j := (finProdFinEquiv.symm i).2
  have jv : j.val=i.val%S := rfl
  change (TraceBitHeader.advicePins 0 _ _ j).toNat=_
  unfold TraceBitHeader.advicePins
  by_cases h : j.val < (1+6*pc+K)*(64*w)
  · rw [dite_eq_left (show 0 ≤ j.val ∧ j.val-0 < (1+6*pc+K)*(64*w) by simpa using h)]
    let t : Fin ((1+6*pc+K)*(64*w)) := ⟨j.val,h⟩
    change (NativeTrace.executable _ t).toNat=_
    rw [NativeTrace.executable_bits]
    have eqv := finProdFinEquiv.apply_symm_apply t
    change (Computability.VPVNP.RAMSerialization.arrayBits _ _ _ t).toNat=_
    rw [←eqv,Computability.VPVNP.RAMSerialization.arrayBits_at,←Computability.VPVNP.LiveHeader.testBit_wordBits,accept_words]
    have rowIndex : (finProdFinEquiv.symm t).1.val=j.val/(64*w) := rfl
    have bitIndex : (finProdFinEquiv.symm t).2.val=j.val%(64*w) := rfl
    rw [rowIndex,bitIndex,jv]
    unfold literalWord
    dsimp only
    by_cases tag : 0 < i.val%S/(64*w) ∧ i.val%S/(64*w) ≤ 6*pc ∧ (i.val%S/(64*w)-1)%6=0
    · rw [ite_eq_left tag,ite_eq_left tag,Fin.val_cast_of_lt hw,Nat.testBit_eq_decide_div_mod_eq,
        Nat.shiftRight_eq_div_pow]
      let bit := 13/2^(i.val%S%(64*w))%2
      change (decide (bit=1)).toNat=bit
      have bound : bit < 2 := Nat.mod_lt _ (by decide)
      by_cases one : bit=1
      · simp [one]
      · have zero : bit=0 := by omega
        simp [zero]
    · rw [ite_eq_right tag,ite_eq_right tag]
      simp
  · rw [dite_eq_right (by simpa using h)]; change 0=_
    have width : 0 < 64*w := by by_contra! z; rw [show 64*w=0 by omega] at hw; norm_num at hw
    have high : 6*pc < j.val/(64*w) := by
      have := (Nat.le_div_iff_mul_le width).mpr (show (1+6*pc+K)*(64*w) ≤ j.val by omega)
      omega
    simp [literalWord,←jv,show ¬ j.val/(64*w) ≤ 6*pc by omega]

def shape (m n B logRadix q S pc : ℕ) : Shape :=
  ⟨m+1,n+1,GridIdleLayout.each m n B,2*B,logRadix,q,S,pc⟩

theorem fits_of_room {W logRadix m n B q S pc : ℕ} (A : GridOrderedSources.Arena)
    (room : Room A (shape m n B logRadix q S pc)) (head : 12*A.J < 2^W)
    (pos : 0 < B) (baseTwo : n+1=2^logRadix) (exp : logRadix*(m+1) < W)
    (pins : S < 2^W) (text : 6*pc < 2^W) (hw : 4 ≤ W) :
    Fits W A (shape m n B logRadix q S pc) := by
  obtain ⟨rails,axes,rows⟩ := room
  have per : 0 < GridIdleLayout.each m n B := by unfold GridIdleLayout.each; positivity
  have near : GridIdleLayout.each m n B ≤ (m+1)*GridIdleLayout.each m n B :=
    Nat.le_mul_of_pos_left _ (by omega)
  have within : 2*B ≤ GridIdleLayout.each m n B :=
    Nat.mul_le_mul_right B (Nat.le_mul_of_pos_right 2 (Nat.pow_pos (Nat.succ_pos n)))
  change (m+1)*GridIdleLayout.each m n B ≤ A.J/8 at rails
  change m+1 ≤ A.J/8 at axes
  change (n+1)^(m+1)*(q*S) ≤ A.J at rows
  refine ⟨?_,baseTwo,exp,per,?_,by omega⟩
  · intro c; cases c <;> dsimp [base,count,shape,Shape.data,Shape.rails,
      GridOrderedSources.Arena.pins,GridOrderedSources.Arena.railMap] <;> omega
  · change GridIdleLayout.each m n B < 2^W ∧ 2*B < 2^W ∧ S < 2^W ∧ 6*pc < 2^W ∧ W < 2^W ∧ 13 < 2^W
    exact ⟨by omega,by omega,pins,text,Nat.lt_two_pow_self,
      lt_of_lt_of_le (show 13 < 2^4 by decide) (Nat.pow_le_pow_right (by decide) hw)⟩

/-- Starting at the decoded compact advice, the native five-pass controller
publishes precisely the Raw interface of the common edge/pin evaluator. -/
theorem raw {F : Type} [Field F] [Fintype F] {m n B logRadix q S pc r K w : ℕ}
    (X : Catalyst.Approximation F (m+1) (q*S)) (enc : FieldCode F (64*w))
    (A : GridOrderedSources.Arena) (hp : 0 < pc) (reserved : ∀ j,X.width j ≤ B)
    (pin : Fin (((m+1)*GridIdleLayout.each m n B)*2)→Bool) (old : Memory (64*w))
    (fit : Fits (64*w) A (shape m n B logRadix q S pc))
    (room : Room A (shape m n B logRadix q S pc))
    (compact : GridApproximationAdvice.wordCount X ≤ A.J)
    (extent : GridApproximationAdvice.wordCount X ≤ 12*B)
    (exterior : ∀ i,old i.val=BitLayout.bitWord (64*w) (pin i)) :
    let b := shape m n B logRadix q S pc
    let lit := GridIdleLayout.literal (w:=w) (r:=r) (K:=K) (q:=q) (S:=S) hp
    let loaded := GridApproximationAdvice.paddedMemory X enc B A.pins.compact old
    (procedure (64*w) A b).Exec loaded (image A b loaded) (cost (64*w) A b) ∧
      GridOrderedSources.Raw X (GridIdleLayout.program X.width reserved lit) enc A B pin
        (image A b loaded) loaded := by
  dsimp only
  let b := shape m n B logRadix q S pc
  let loaded := GridApproximationAdvice.paddedMemory X enc B A.pins.compact old
  have lows := image_low A b loaded
  have get := fun (c : Column) (i : ℕ) (hi : i < count b c) => image_at room c i hi loaded
  have powers (j : Fin (m+1)) : image A b loaded (A.railMap.powers+j.val)=
      (((n+1)^j.val : ℕ) : Word (64*w)) := get .powers j.val j.isLt
  refine ⟨exec fit _,⟨⟨?_,fun j => by simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using powers j,?_,?_⟩,?_⟩⟩
  · intro e
    refine ⟨?_,?_,powers _,get .touch e.val e.isLt⟩
    · change _=((GridIdleLayout.direction e).val : Word (64*w))
      rw [GridIdleLayout.direction_val]; exact get .direction e.val e.isLt
    · change _=((finFunctionFinEquiv (GridIdleLayout.row e)).val : Word (64*w))
      rw [GridIdleLayout.row_val]; exact get .cell e.val e.isLt
  · intro c i
    let a := (finFunctionFinEquiv c).val*(q*S)+i.val
    have cell := (finFunctionFinEquiv c).isLt
    have hi : a < count b .data := by
      change _ < (n+1)^(m+1)*(q*S)
      have step : (finFunctionFinEquiv c).val+1 ≤ (n+1)^(m+1) := by simpa using cell
      have till := Nat.mul_le_mul_right (q*S) step
      rw [Nat.add_mul,one_mul] at till
      dsimp [a]; have := i.isLt; omega
    have got := get .data a hi
    change _ = ((GridIdleLayout.literal (w:=w) (r:=r) (K:=K) hp i).toNat : Word (64*w))
    rw [accept_at hp fit.scalar.2.2.2.2.2]
    have red : a%S=i.val%S := by simp [a,Nat.add_mod,Nat.mul_mod]
    change image A b loaded (A.pins.data+a)=(literalWord (64*w) S pc a : Word (64*w)) at got
    have same : literalWord (64*w) S pc a=literalWord (64*w) S pc i.val := by
      unfold literalWord
      rw [red]
    exact got.trans (congrArg (fun v : ℕ => (v : Word (64*w))) same)
  · intro i hi
    have dst : A.pins.compact+i < 5*A.J := by dsimp [GridOrderedSources.Arena.pins]; omega
    rw [lows _ dst]
    simp [loaded,GridApproximationAdvice.paddedMemory,fillSegment,lt_of_lt_of_le hi extent]
  · intro i
    have hr := room.rails
    have h := i.isLt
    change i.val < (m+1)*GridIdleLayout.each m n B*2 at h
    change (m+1)*GridIdleLayout.each m n B ≤ A.J/8 at hr
    have low : i.val < 2*A.J := by omega
    rw [lows _ (by omega)]
    change GridApproximationAdvice.paddedMemory X enc B (2*A.J) old i.val=_
    simpa [GridApproximationAdvice.paddedMemory,fillSegment,show ¬2*A.J ≤ i.val by omega] using exterior i

/-- Both total duration and text have uniform constants, including the native
address arithmetic which inserts the zero transverse digit. -/
theorem work_bound (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (c : Column) :
    (expr W A b c).work ≤ 128 := by
  cases c <;> exact of_decide_eq_true rfl

private theorem cost_columns (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) :
    cost W A b ≤ 20+260*(3*b.rails+b.axes+b.data) := by
  have f (c : Column) : fee W A b c ≤ 4+count b c*260 := by
    unfold fee
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by have := work_bound W A b c; omega)) _
  have hd := f .direction
  have hc := f .cell
  have hp := f .powers
  have ht := f .touch
  have hw := f .data
  dsimp only [cost,count] at *
  omega

theorem cost_bound (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) :
    cost W A b ≤ 20+1000*(b.rails+b.axes+b.data) := by
  have := cost_columns W A b
  omega

theorem text_bound (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) :
    let M := procedure W A b
    M.labels+M.registers+M.slots ≤ 10000 := by
  have bound := work_bound W A b
  have bound' (c : Column) := HeaderScan.binds_closed (w:=W) (expr W A b c)
  simp only [procedure,Procedure.seq,scan,PhysicalInputPhases.writing,DescriptorExpr.Term.labels_eq,
    bound']
  have := bound .direction; have := bound .cell; have := bound .powers; have := bound .touch
  have := bound .data; omega

theorem work_in_cells (W : ℕ) (A : GridOrderedSources.Arena) (m n B h q S pc : ℕ)
    (sized : q*S ≤ B) (pos : 0 < B) :
    cost W A (shape m n B h q S pc) ≤ 20+3000*(m+1)*((n+1)^(m+1)*B) := by
  have h₁ : 1 ≤ (n+1)^(m+1)*B := Nat.mul_pos (pow_pos (by omega) _) pos
  have inc : (n+1)^m ≤ (n+1)^(m+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have rails := Nat.mul_le_mul_left (m+1) (Nat.mul_le_mul_right B (Nat.mul_le_mul_left 2 inc))
  have data := Nat.mul_le_mul_left ((n+1)^(m+1)) sized
  have axis := Nat.mul_le_mul_left (m+1) h₁
  have large := Nat.le_mul_of_pos_left ((n+1)^(m+1)*B) (show 0 < m+1 from Nat.zero_lt_succ _)
  apply (cost_columns W A (shape m n B h q S pc)).trans
  dsimp only [shape,Shape.rails,Shape.data,GridIdleLayout.each]
  nlinarith only [rails,data,axis,large]

/-- The zero-flag branch first checks the complete unused suffix. -/
def guarded (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (cap : ℕ) : Procedure W :=
  (GridIdleGuard.procedure W (13*A.J) (12*A.J+1) cap).seq (procedure W A b)

def guardedCost (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (cap : ℕ) : ℕ :=
  GridIdleGuard.cost (13*A.J) (12*A.J+1) cap+cost W A b

theorem guard_price (A : GridOrderedSources.Arena) (cap : ℕ) :
    GridIdleGuard.cost (13*A.J) (12*A.J+1) cap ≤ 500*(cap+1) := by
  let f := TerminalWireArchive.checkWord (GridSelector.layout (13*A.J) (13*A.J+2) (12*A.J+1) cap)
  have op : f.work ≤ 100 := of_decide_eq_true rfl
  have pace := Nat.mul_le_mul_left (cap+1) (show 2*f.work+4 ≤ 204 by omega)
  have guard : GridIdleGuard.cost (13*A.J) (12*A.J+1) cap ≤ 500*(cap+1) := by
    change 4+3*(2*11+4)+(6+(cap+1)*(2*f.work+4)) ≤ _
    omega
  exact guard

theorem guarded_cost_bound (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (cap : ℕ) :
    guardedCost W A b cap ≤ 500*(cap+1)+20+1000*(b.rails+b.axes+b.data) := by
  have guard := guard_price A cap
  have h := cost_bound W A b
  unfold guardedCost; omega

theorem guarded_text_bound (W : ℕ) (A : GridOrderedSources.Arena) (b : Shape) (cap : ℕ) :
    let M := guarded W A b cap
    M.labels+M.registers+M.slots ≤ 12000 := by
  let G := GridIdleGuard.procedure W (13*A.J) (12*A.J+1) cap
  have hG : G.labels+G.registers+G.slots ≤ 2000 := by
    dsimp only [G,GridIdleGuard.procedure,Procedure.seq,TerminalWireArchive.check,
      ProtocolRAM.scan,PhysicalInputPhases.writing]
    simp only [DescriptorExpr.Term.labels_eq,HeaderScan.binds_closed,ProtocolRAM.compile_binds]
    exact of_decide_eq_true rfl
  have rest := text_bound W A b
  change G.labels+(procedure W A b).labels+(G.registers+(procedure W A b).registers)+
    (G.slots+(procedure W A b).slots) ≤ 12000
  omega

/-- The actual captured input contains the high selector separately from the
packed approximation. An invalid trailing bit loses all its native mass. -/
theorem guarded_admission {F : Type} [Field F] [Fintype F]
    {m n B logRadix q S pc r K w d cap tp tr tk ep er ek : ℕ}
    (X : Catalyst.Approximation F (m+1) (q*S)) (enc : FieldCode F (64*w))
    (params : Fin d→Word (64*w)) (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
    (A : GridOrderedSources.Arena) (hp : 0 < pc) (reserved : ∀ j,X.width j ≤ B)
    (pin : Fin (((m+1)*GridIdleLayout.each m n B)*2)→Bool) (s : Fin (cap+1)→Bool)
    (fit : Fits (64*w) A (shape m n B logRadix q S pc))
    (room : Room A (shape m n B logRadix q S pc))
    (extent : GridApproximationAdvice.wordCount X ≤ 12*B) (payload : 12*B ≤ A.J)
    (ticks : cap < A.J) (head : 13*A.J+3 < 2^(64*w))
    (sourceRoom : GridSelfHeader.rawSize w ((m+1)*GridIdleLayout.each m n B) B d ≤ 12*A.J) :
    let b := shape m n B logRadix q S pc
    let lit := GridIdleLayout.literal (w:=w) (r:=r) (K:=K) (q:=q) (S:=S) hp
    let old := GridSelfHeader.captured (B:=B) X enc params recv eval pin (12*A.J) s
    let loaded := GridApproximationAdvice.paddedMemory X enc B A.pins.compact old
    let M := guarded (64*w) A b cap
    TickStageSpec.Admission enc M.block M.publicData (·=loaded) (fun _=>∀i,Fin.tail s i=false)
      (fun _ out => GridOrderedSources.Raw X (GridIdleLayout.program X.width reserved lit) enc A B pin
        out loaded) (guardedCost (64*w) A b cap) := by
  dsimp only
  let b := shape m n B logRadix q S pc
  let old := GridSelfHeader.captured (B:=B) X enc params recv eval pin (12*A.J) s
  let load := GridApproximationAdvice.paddedMemory X enc B A.pins.compact
  let m₀ := load old
  let first := GridIdleGuard.procedure (64*w) (13*A.J) (12*A.J+1) cap
  let next := procedure (64*w) A b
  let mid := GridIdleGuard.warm (13*A.J) cap m₀
  have ext (i) := GridSelfHeader.external_at X enc params recv eval pin sourceRoom s i
  have rlim := room.rails
  change (m+1)*GridIdleLayout.each m n B ≤ A.J/8 at rlim
  have loc (i : Fin cap) : m₀ (12*A.J+1+i.val)=BitLayout.bitWord (64*w) (Fin.tail s i) := by
    have outside : ¬(2*A.J ≤ 12*A.J+1+i.val ∧ 12*A.J+1+i.val < 2*A.J+12*B) := by omega
    change GridApproximationAdvice.paddedMemory X enc B (2*A.J) old _=_
    simp only [GridApproximationAdvice.paddedMemory,fillSegment,ite_eq_right outside]
    have addr : 12*A.J+1+i.val=12*A.J+i.succ.val := by simp [Nat.add_assoc,Nat.add_comm]
    rw [addr]; exact GuessLoop.install_get _ _ _ _
  have guard : TickStageSpec.Admission enc first.block first.publicData (·=m₀)
      (fun _ => ∀ i,Fin.tail s i=false) (fun _ o => o=mid)
      (GridIdleGuard.cost (13*A.J) (12*A.J+1) cap) :=
    GridIdleGuard.admission enc (13*A.J) (12*A.J+1) cap (Fin.tail s) m₀ head (by omega) fit.width loc
  have partition (a : ℕ) (ha : 2*A.J ≤ a ∧ a < 2*A.J+12*B) : mid a=m₀ a :=
    GridIdleGuard.frame _ _ _ _ (Or.inl (by omega))
  have stable : load mid=mid := by
    funext a
    by_cases h : 2*A.J ≤ a ∧ a < 2*A.J+12*B
    · rw [partition a h]; change fillSegment (2*A.J) (12*B) _ mid a=fillSegment (2*A.J) (12*B) _ old a
      simp [fillSegment,h]
    · change fillSegment (2*A.J) (12*B) _ mid a=_; simp [fillSegment,h]
  have pins (i : Fin (((m+1)*GridIdleLayout.each m n B)*2)) : mid i.val=BitLayout.bitWord (64*w) (pin i) := by
    have := i.isLt
    have low : i.val < 2*A.J := by omega
    change GridIdleGuard.warm _ _ _ _=_
    rw [GridIdleGuard.frame _ _ _ _ (Or.inl (by omega))]
    have hx : old i.val=((pin i).toNat:Word (64*w)) := ext i
    have lowRead : m₀ i.val=old i.val := by
      change fillSegment (2*A.J) (12*B) _ old i.val=_
      simp [fillSegment,show ¬(2*A.J ≤ i.val) by omega]
    rw [lowRead,hx]
    cases pin i <;> rfl
  let setting := GridIdleLayout.program (n:=n) X.width reserved (GridIdleLayout.literal (w:=w) (r:=r) (K:=K) (q:=q) (S:=S) hp)
  have done : next.Exec (load mid) (image A b (load mid)) (cost _ A b) ∧
      GridOrderedSources.Raw X setting enc A B pin (image A b (load mid)) (load mid) :=
    raw X enc A (r:=r) (K:=K) hp reserved pin mid fit room (extent.trans payload) extent pins
  rw [stable] at done
  have output : GridOrderedSources.Raw X setting enc A B pin (image A b mid) m₀ := by
    obtain ⟨v,ex⟩ := done.2
    refine ⟨⟨v.controller,v.powers,v.localData,?_⟩,ex⟩
    intro i hi
    rw [v.compact i hi,GridApproximationAdvice.paddedMemory_eq _ _ _ _ _ _ hi extent,
      GridApproximationAdvice.paddedMemory_eq _ _ _ _ _ _ hi extent,
      GridApproximationAdvice.packed_at _ _ _ _ _ hi,GridApproximationAdvice.packed_at _ _ _ _ _ hi]
  have whole : TickStageSpec.Admission enc (first.seq next).block (first.seq next).publicData
      (·=m₀) (fun _ => ∀ i,Fin.tail s i=false)
      (fun _ o => ∃ tmp : Memory (64*w), tmp=mid ∧ o=image A b mid)
      (guardedCost (64*w) A b cap) :=
    TickStageSpec.admission_seq enc first next guard (TickStageSpec.admission_of_spec enc next done.1)
      (fun _ _ h=>h) (fun _ _ _ good post=>⟨post,⟨fun _=>good,fun _=>trivial⟩⟩)
  intro P R K₁ M pc' reg pub exit inst data cfg mem beginAt hm
  obtain ⟨yes,no⟩ := whole M pc' reg pub exit inst data cfg mem beginAt hm
  refine ⟨fun ok => ?_,no⟩
  obtain ⟨time,ht,st,o,reached,⟨tmp,hg,returned⟩,advance⟩ := yes ok
  exact ⟨time,ht,st,o,reached,by rw [returned]; exact output,advance⟩

/-- The writer's own verified geometric sizes supply the idle publisher's
five memory regions and every arithmetic operand checked by the row ROM. -/
theorem fits_from_pages {F : Type} [Field F] [Fintype F] {m n B logRadix q S pc w : ℕ}
    (X : Catalyst.Approximation F (m+1) (q*S))
    (rails : (m+1)*GridIdleLayout.each m n B ≤ GridDescription.sector w/8)
    (axes : m+1 ≤ GridDescription.sector w/8)
    (pinData : (n+1)^(m+1)*(q*S) ≤ GridDescription.sector w)
    (packed : 12*B ≤ GridDescription.sector w)
    (age : 1 ≤ w) (pos : 0 < B) (teams : 0 < q) (sized : X.size ≤ B) (baseTwo : n+1=2^logRadix)
    (volume : (n+1)^(m+1)*B ≤ 2^(2*w)) (text : pc ≤ GridDescription.capacity w) :
    let A : GridOrderedSources.Arena := ⟨GridDescription.sector w⟩
    let b := shape m n B logRadix q S pc
    Fits (64*w) A b ∧ Room A b := by
  let J := GridDescription.sector w
  have high : 64*J < 2^(64*w) := GridDescription.sectors_fit age
  have room : Room (⟨GridDescription.sector w⟩ : GridOrderedSources.Arena) (shape m n B logRadix q S pc) :=
    ⟨rails,axes,pinData⟩
  have nbits : 2^(logRadix*(m+1)) ≤ 2^(2*w) := by
    rw [pow_mul,←baseTwo]; exact (Nat.le_mul_of_pos_right _ pos).trans volume
  have exp : logRadix*(m+1) ≤ 2*w := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp nbits
  have p := (GridApproximationAdvice.data_le_size X).trans sized
  have sc := Nat.le_mul_of_pos_left S teams
  have fb := packed
  change 12*B ≤ J at fb
  have pcap : pc ≤ w := text.trans (Nat.div_le_self w 1024)
  refine ⟨fits_of_room _ room (by change 12*J < _; omega) pos baseTwo (by omega)
    (by omega) (by have : 64*w < 2^(64*w) := Nat.lt_two_pow_self; omega) (by omega),room⟩

end
end Hierarchy.GridControllerIdle

end OAI
