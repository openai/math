import OAI.Hierarchy.GridPinPublisherLayout
import OAI.Hierarchy.GridPinHeaderNative
import OAI.Hierarchy.GridSelfHeader
import Mathlib.Data.List.OfFn

namespace OAI
/-! # The actual self-programmed header published by a native pin scan -/

namespace Hierarchy.GridPinHeaderNative
open GridReceiverHeader
open ThreeFlat ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

private def digits (W : ℕ) (x : Word W) : List Bool :=
  List.ofFn fun j : Fin W => x.val.testBit (W-1-j.val)

private theorem serialized {W d : ℕ} (f : Fin d→Word W) :
    List.ofFn (wordBits W f)=(List.ofFn f).flatMap (digits W) := by
  rw [List.ofFn_mul,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have pos : 0<W := Nat.zero_lt_of_lt j.isLt
  change wordBits W f ⟨i.val*W+j.val,_⟩=(f i).val.testBit (W-1-j.val)
  convert word_at f i j using 2; apply Fin.ext; dsimp [finProdFinEquiv]; ring

private theorem header_flat {w n ell text : ℕ} (fits : text≤w^2) (raw : Fin (w^2)→Bool)
    (idx : Word (64*w)) (params : Fin n→Word (64*w)) (sel : Fin ell→Bool) :
    header text fits raw idx params sel =
      List.ofFn (fun i : Fin text=>raw (i.castLE fits)) ++ (digits (64*w) idx ++
        (List.ofFn (wordBits (64*w) (GridSelfHeader.words params)) ++ List.ofFn sel)) := by
  rw [header,serialized,serialized,serialized]
  have h : List.ofFn (GridSelfHeader.words params)=List.ofFn params ++ List.ofFn (thresholdWords w) :=
    List.ofFn_fin_append params (thresholdWords w)
  rw [h,List.flatMap_append,List.ofFn_cons]
  simp [List.append_assoc]

/-- The scanner's one output word at a public tick's ordinal and one local
pin agrees with the actual concatenated program/operand/selector header. -/
theorem initialWord_header {w n ell text : ℕ} (pos : 0<w)
    (B : Banks) (m : ℕ→ℕ) (fits : text≤w^2) (raw : Fin (w^2)→Bool)
    (params : Fin n→Word (64*w)) (sel : Fin ell→Bool) (t p : ℕ)
    (tfit : t<2^(64*w)) (pfit : p<B.pins)
    (textLen : B.text=text) (operandLen : B.operandBits=(n+count w)*(64*w))
    (selLen : B.selector=ell)
    (textAt : ∀ i : Fin text, m (B.textBase+i.val)=(raw (i.castLE fits)).toNat)
    (operandAt : ∀ i : Fin ((n+count w)*(64*w)), m (B.operandBase+i.val)=
      (wordBits (64*w) (GridSelfHeader.words params) i).toNat)
    (selAt : ∀ i : Fin ell, m (B.selectorBase+i.val)=(sel i).toNat) :
    initialWord (64*w) B m (B.literalBase+(p+B.pins*t)) =
      ((header text fits raw (t:Word (64*w)) params sel)[p]?.getD false).toNat := by
  have wp : 0<64*w := by omega
  have bp : 0<B.pins := Nat.zero_lt_of_lt pfit
  rw [header_flat,initialWord]
  simp only [Nat.add_sub_cancel_left,Nat.add_mul_div_left _ _ bp,Nat.div_eq_of_lt pfit,
    Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt pfit,textLen,operandLen,selLen]
  simp only [List.getElem?_append,List.length_ofFn,List.getElem?_ofFn,digits]
  by_cases a : p<text
  · simp [a,textAt ⟨p,a⟩]
  by_cases b : p-text<64*w
  · simp [a,b,bitWord_test wp,Nat.mod_eq_of_lt b,Fin.val_cast_of_lt tfit]
  by_cases c : p-text-64*w<(n+count w)*(64*w)
  · simp [a,b,c,operandAt ⟨_,c⟩]
  by_cases d : p-text-64*w-(n+count w)*(64*w)<ell
  · simp [a,b,c,d,selAt ⟨_,d⟩]
  · simp [a,b,c,d]

theorem captured_header {F : Type} [Field F] [Fintype F]
    {w k f e compact n ell tp tr tk ep er ek : ℕ}
    (X : Catalyst.Approximation F k f) (enc : FieldCode F (64*w))
    (params : Fin n→Word (64*w)) (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
    (x : Fin (e*2)→Bool) {start literal pins text : ℕ} (sel : Fin ell→Bool)
    (sep : GridSelfHeader.rawSize w e compact n≤ start) (fit : text≤w^2)
    (pos : 0<w) (t p : ℕ) (tfit : t<2^(64*w)) (pfit : p<pins) :
    let view := GridSelfHeader.captured (B:=compact) X enc params recv eval x start sel
    let bank := captureBanks w e compact n ell start literal pins text
    let raw := GridDescription.code (q:=w^2) recv eval
    initialWord (64*w) bank (fun z=>(view z).val) (literal+(p+pins*t)) =
      ((header text fit raw (t:Word (64*w)) params sel)[p]?.getD false).toNat := by
  intro view bank raw
  have bits (b : Bool) : ((b.toNat:Word (64*w))).val=b.toNat := by
    apply Fin.val_cast_of_lt
    have high : 1<2^(64*w) := Nat.one_lt_two_pow (by omega)
    cases b <;> simp; omega
  apply initialWord_header pos bank (fun z=>(view z).val) fit raw params sel t p tfit pfit rfl rfl rfl
  · intro i
    have sz : e*2+i.val<GridSelfHeader.rawSize w e compact n := by
      dsimp [GridSelfHeader.rawSize]; have := i.isLt; omega
    have h := GridSelfHeader.input_at X enc params recv eval x sep sel ⟨e*2+i.val,sz⟩
    change (view (e*2+i.val)).val=_
    rw [show view (e*2+i.val)=_ from h,bits]
    exact congrArg Bool.toNat (GridDescription.code_at x _ _ (i.castLE fit))
  · intro i
    have h := GridSelfHeader.operand_at X enc params recv eval x sep sel i
    change (view (e*2+w^2+compact*w^2+i.val)).val=_
    rw [Nat.add_assoc (e*2+w^2) _ _,show view _=_ from h,bits]
  · intro i
    change (RAM.GuessLoop.install start sel _ (start+i.val)).val=(sel i).toNat
    rw [RAM.GuessLoop.install_get]
    exact bits (sel i)

end Hierarchy.GridPinHeaderNative

end OAI
