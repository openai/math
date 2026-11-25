import OAI.ThreeFlat.Diagonal.CompressorNativeExpr
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.CompressorTagScan

namespace OAI
/-! # The tag-offset row reads the old graph and mutable preceding offsets -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open Ordered
open scoped Fin.NatCast
variable {w k n d t : ℕ}

structure TagColumns (w k n : ℕ) where
  offsets : Term w k n
  outDst : Term w k n
  inSrc : Term w k n
  outShift : Term w k n
  inShift : Term w k n

def stepTerms (T : TagColumns w k n) (d : ℕ) (v : Term w k n) : List (Term w k n) :=
  .literal 0 :: List.ofFn (fun i : Fin d => readSlot T.outShift v d i)

def xor (a b : Term w k n) : Term w k n := .binary .bitXor a b

def tagTerms (T : TagColumns w k n) (d : ℕ) (v src dst neighbor delta : Term w k n) :
    List (Term w k n) :=
  (stepTerms T d v).map (xor delta) ++ (stepTerms T d src).flatMap fun a =>
    (stepTerms T d dst).map fun b => xor (xor (xor delta a) b) (readRow T.offsets neighbor)

def tagDirection (T : TagColumns w k n) (v : Term w k n) : Fin d ⊕ Fin d → List (Term w k n)
  | .inl i =>
    let dst := readSlot T.outDst v d i
    tagTerms T d v v dst dst (readSlot T.outShift v d i)
  | .inr i =>
    let src := readSlot T.inSrc v d i
    tagTerms T d v src v src (readSlot T.inShift v d i)

def offsetRow (T : TagColumns w k 1) (d t : ℕ) : Term w k 1 :=
  firstFree ((directions d).flatMap (tagDirection T (.binary .sub (.result 0) T.offsets))) 0
    (List.ofFn fun i : Fin (2^t) => (i.val : Word w))

/-- The five columns are interpreted through public bases. Inbound shifts
belong to the old outgoing edge whose incoming port is being visited. -/
structure TagReads {V : Type*} (T : TagColumns w k n) (G : SlotGraph V d)
    (shift : V × Fin d → BitWord t) (offset : V → BitWord t) (fit : t ≤ w)
    (addr : V → Word w) (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) : Prop where
  outDst : ∀ (x : V) (i : Fin d), m (T.outDst.eval pub m vs + addr x * (d : Word w) + (i.val : Word w)).val =
    addr (G.target (x,i)).1
  inSrc : ∀ (x : V) (i : Fin d), m (T.inSrc.eval pub m vs + addr x * (d : Word w) + (i.val : Word w)).val =
    addr (G.target.symm (x,i)).1
  outShift : ∀ (x : V) (i : Fin d), m (T.outShift.eval pub m vs + addr x * (d : Word w) + (i.val : Word w)).val =
    tagWord fit (shift (x,i))
  inShift : ∀ (x : V) (i : Fin d), m (T.inShift.eval pub m vs + addr x * (d : Word w) + (i.val : Word w)).val =
    tagWord fit (shift (G.target.symm (x,i)))
  offsets : ∀ x, m (T.offsets.eval pub m vs + addr x).val = tagWord fit (offset x)

variable {V : Type*} {T : TagColumns w k n} {G : SlotGraph V d}
variable {shift : V × Fin d → BitWord t} {offset : V → BitWord t} {fit : t ≤ w}
variable {addr : V → Word w} {pub : Fin k → Word w} {m : Memory w} {vs : Fin n → Word w}
variable (R : TagReads T G shift offset fit addr pub m vs)
include R

theorem eval_stepTerms (v : Term w k n) (x : V) (hv : v.eval pub m vs = addr x) :
    (stepTerms T d v).map (fun z => z.eval pub m vs) = (stepsList shift x).map (tagWord fit) := by
  simp [stepTerms,stepsList,List.map_ofFn,Function.comp_def,eval_readSlot,hv,R.outShift,tagWord_zero]

private theorem eval_terms (v src dst nbr delta : Term w k n) (x source target other : V)
    (s : BitWord t) (hv : v.eval pub m vs = addr x) (hs : src.eval pub m vs = addr source)
    (ht : dst.eval pub m vs = addr target) (hn : nbr.eval pub m vs = addr other)
    (hd : delta.eval pub m vs = tagWord fit s) :
    (tagTerms T d v src dst nbr delta).map (fun z => z.eval pub m vs) =
      ((stepsList shift x).map (fun a => s+a) ++ (stepsList shift source).flatMap fun a =>
        (stepsList shift target).map fun b => s+a+b-offset other).map (tagWord fit) := by
  let ev := fun z : Term w k n => z.eval pub m vs
  let ex := stepTerms T d v
  let es := stepTerms T d src
  let et := stepTerms T d dst
  have eqv := eval_stepTerms R v x hv
  have eqs := eval_stepTerms R src source hs
  have eqt := eval_stepTerms R dst target ht
  let add := BinaryOp.bitXor.eval (w:=w)
  let right (A : List (Word w)) (B : List (Word w)) :=
    A.flatMap fun a => B.map fun b => add (add (add (tagWord fit s) a) b) (tagWord fit (offset other))
  calc
    _ = (ex.map ev).map (add (tagWord fit s)) ++ right (es.map ev) (et.map ev) := by
      simp [tagTerms,ex,es,et,right,List.map_flatMap,List.flatMap_map,List.map_map,
        Function.comp_def,ev,xor,hd,eval_readRow,hn,R.offsets,add]
    _ = _ := by
      dsimp only [ex,es,et,ev]
      rw [eqv,eqs,eqt]
      simp [right,add,List.map_flatMap,List.flatMap_map,List.map_map,
        Function.comp_def,tagWord_add,tagWord_sub]

theorem eval_tagDirection (v : Term w k n) (x : V) (hv : v.eval pub m vs = addr x)
    (i : Fin d ⊕ Fin d) : (tagDirection T v i).map (fun z => z.eval pub m vs) =
      (tagPart G shift x offset i).map (tagWord fit) := by
  cases i with
  | inl i =>
    apply eval_terms R _ _ _ _ _ _ _ _ _ _ hv hv
    · simp [eval_readSlot,hv,R.outDst,incident]
    · simp [eval_readSlot,hv,R.outDst,adjacent]
    · simp [eval_readSlot,hv,R.outShift,incident]
  | inr i =>
    simp only [tagPart,incident,adjacent,Equiv.apply_symm_apply]
    apply eval_terms R _ _ _ _ _ _ _ _ _ _ hv _ hv
    · simp [eval_readSlot,hv,R.inSrc]
    · simp [eval_readSlot,hv,R.inShift]
    · simp [eval_readSlot,hv,R.inSrc]

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
