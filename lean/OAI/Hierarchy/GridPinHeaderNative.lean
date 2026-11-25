import OAI.Hierarchy.GridPinHeaderSource
import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Initializing every receiver's real program header and zero padding -/

namespace Hierarchy.GridPinHeaderNative
open ThreeFlat.RAM PhysicalPinsExpr PhysicalProcedure DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

set_option maxRecDepth 18000
set_option maxHeartbeats 1000000

private abbrev X := Formula 1
private abbrev add (x y : X) : X := .op .add x y
private abbrev lit (x : ℕ) : X := .lit x
private abbrev loadAt (b : ℕ) (i : X) : X := .load (add (lit b) i)
private abbrev divBy (x : X) (b : ℕ) : X := .op .div x (lit b)
private abbrev modBy (x : X) (b : ℕ) : X := .op .mod x (lit b)

/-- Produce a bit of a captured or computed word in the receiver's big-endian format. -/
private def wordBit (W : ℕ) (x k : X) : X :=
  .op .bitAnd (.op .shiftRight x (.cut (lit (W-1)) (modBy k W))) (lit 1)

/-- All cells share this expression. The row address selects the tick's actual
ordinal and the word to inspect. Every remaining slot initializes to zero. -/
def headerExpr (W : ℕ) (B : Banks) : X :=
  let a := Formula.cut (.reg 0) (lit B.literalBase)
  let t := divBy a B.pins
  let p := modBy a B.pins
  let k := Formula.cut p (lit B.text)
  let u := Formula.cut k (lit W)
  let s := Formula.cut u (lit B.operandBits)
  .select .lt p (lit B.text) (loadAt B.textBase p)
    (.select .lt k (lit W) (wordBit W t k)
      (.select .lt u (lit B.operandBits) (loadAt B.operandBase u)
        (.select .lt s (lit B.selector) (loadAt B.selectorBase s) (lit 0))))

/-- The program text and its time per scanned pin are independent of the number of inputs. -/
@[simp] theorem header_work (W : ℕ) (B : Banks) : (headerExpr W B).work=376 := rfl

private def bitWord (W j word : ℕ) : ℕ :=
  (if W-1-j%W<W then word >>> (W-1-j%W) else 0) &&& 1

def initialWord (W : ℕ) (B : Banks) (m : ℕ→ℕ) (address : ℕ) : ℕ :=
  let a := address-B.literalBase
  let t := a/B.pins
  let p := a%B.pins
  let k := p-B.text
  let u := k-W
  let s := u-B.operandBits
  if p<B.text then m (B.textBase+p)
  else if k<W then bitWord W k t
  else if u<B.operandBits then m (B.operandBase+u)
  else if s<B.selector then m (B.selectorBase+s) else 0

private theorem branch_lt {α : Sort*} (x y : ℕ) (yes no : α) :
    (if natTest .lt x y then yes else no) = (if x<y then yes else no) := by
  by_cases h : x<y
  · have test : natTest .lt x y=true := decide_eq_true h
    exact (ite_eq_left test).trans (ite_eq_left h).symm
  · have test : ¬natTest .lt x y=true := fun eq => h (of_decide_eq_true eq)
    exact (ite_eq_right test).trans (ite_eq_right h).symm

theorem expr_natural (W : ℕ) (B : Banks) (m : ℕ→ℕ) (a : ℕ) :
    (headerExpr W B).natural W (fun _=>0) m (fun _=>a)=initialWord W B m a := by
  simp [headerExpr,initialWord,Formula.natural,wordBit,bitWord,natOp,branch_lt,
    add,lit,loadAt,divBy,modBy]
  split_ifs <;> simp_all [natTest]; omega

theorem bitWord_test {W : ℕ} (pos : 0<W) (j word : ℕ) :
    bitWord W j word=(word.testBit (W-1-j%W)).toNat := by
  have h : W-1-j%W<W := by omega
  rw [bitWord,ite_eq_left h,Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow,Nat.testBit_eq_decide_div_mod_eq]
  have b := Nat.mod_lt (word/2^(W-1-j%W)) (by decide : 0<2)
  let digit := word/2^(W-1-j%W)%2
  change digit=(decide (digit=1)).toNat
  by_cases h1 : digit=1
  · simp [h1]
  · have h0 : digit=0 := by change digit<2 at b; omega
    simp [h0]

/-- Fixed header-scan text. The program itself only contains numeric addresses
and sizes, and reads every nonordinal header field from the captured memory. -/
def procedure (W ticks : ℕ) (B : Banks) : Procedure W :=
  PhysicalInputPhases.writing (HeaderScan.closed (headerExpr W B)) Fin.elim0 B.literalBase (ticks*B.pins)

theorem initialWord_congr (W : ℕ) (B : Banks) (m o : ℕ→ℕ) (a : ℕ)
    (same : ∀ z, source B z → o z=m z) : initialWord W B o a=initialWord W B m a := by
  unfold initialWord
  dsimp only
  split_ifs with text idx operand sel
  · exact same _ (Or.inl ⟨by omega,by omega⟩)
  · rfl
  · exact same _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
  · exact same _ (Or.inr (Or.inr ⟨by omega,by omega⟩))
  · rfl

/-- Every selected dereference fits in one word using just the lengths of the
three authentic input arrays. The unselected arms need no range premise. -/
theorem header_fits (W : ℕ) (B : Banks) (a : Word W) (m : ℕ→ℕ)
    (pos : 0<W) (pins : 0<B.pins) (pinFit : B.pins<2^W)
    (literal : B.literalBase<2^W) (text : B.textBase+B.text<2^W)
    (ops : B.operandBase+B.operandBits<2^W) (sel : B.selectorBase+B.selector<2^W) :
    (headerExpr W B).Fits W (fun _=>0) m (fun _=>a.val) := by
  let x := a.val-B.literalBase
  let p := x%B.pins
  let t := x/B.pins
  let k := p-B.text
  let j := k%W
  have bound : x<2^W := (Nat.sub_le ..).trans_lt a.isLt
  have row : p<B.pins := Nat.mod_lt _ pins
  have tick : t<2^W := (Nat.div_le_self ..).trans_lt bound
  have digit : j<W := Nat.mod_lt _ pos
  have width := Nat.lt_two_pow_self (n:=W)
  have one := Nat.one_lt_two_pow (by omega : W≠0)
  have shift := Nat.shiftRight_le t (W-1-j)
  have shifted : (if W-1-j<W then t >>> (W-1-j) else 0)<2^W := by
    rw [ite_eq_left (by omega : W-1-j<W)]
    exact shift.trans_lt tick
  simp only [headerExpr,wordBit,modBy,divBy,loadAt,add,lit,Formula.Fits,Formula.natural,
    opFits,natOp,branch_lt,true_and]
  have address := a.isLt
  dsimp only [j,k,t,p,x] at bound row tick digit shift shifted
  split_ifs
  all_goals (repeat' apply And.intro)
  all_goals first | trivial | omega

theorem procedure_spec (W : ℕ) (B : Banks) (ticks : ℕ) (m : Memory W)
    (valid : B.literalBase+ticks*B.pins<2^W)
    (apart : ∀ z, source B z → z<B.literalBase ∨ B.literalBase+ticks*B.pins≤z)
    (pos : 0<W) (pins : 0<B.pins) (pinFit : B.pins<2^W)
    (text : B.textBase+B.text<2^W) (ops : B.operandBase+B.operandBits<2^W)
    (sel : B.selectorBase+B.selector<2^W) :
    (procedure W ticks B).Spec (·=m)
      (fun _ out=>out=fillSegment B.literalBase (ticks*B.pins)
        (fun a=>(initialWord W B (fun j=>(m j).val) a : Word W)) m)
      (4+ticks*B.pins*(2*(headerExpr W B).work+4)) := by
  rw [← HeaderScan.binds_closed (w:=W) (headerExpr W B)]
  let word := fun a : ℕ => (initialWord W B (fun j=>(m j).val) a : Word W)
  intro P R K M pc reg pub exit hi hd c m₀ start hm
  subst m₀
  exact PhysicalInputPhases.writing_spec (HeaderScan.closed (headerExpr W B)) Fin.elim0
    B.literalBase (ticks*B.pins) valid (·=m) word (by
    rintro _ rfl a o lo hi agree
    rw [HeaderScan.eval_closed]
    have atWord := (headerExpr W B).value_eq_natural (w:=W) (fun _=>0) (fun i=>(o i).val)
      (fun _=>a.val) (header_fits W B a _ pos pins pinFit (by omega) text ops sel)
    simp only [Nat.cast_zero,Fin.cast_val_eq_self,expr_natural] at atWord
    exact atWord.trans (congrArg (fun x : ℕ => (x:Word W))
      (initialWord_congr W B _ _ a.val (fun j hj => congrArg Fin.val (agree j (apart j hj))))))
    M pc reg pub exit hi hd c m start rfl

end Hierarchy.GridPinHeaderNative

end OAI
