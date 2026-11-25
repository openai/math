import OAI.ThreeFlat.Diagonal.CompressorNodeHalves
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # Physical source, polarity, width and prefix at each numbered slot -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

open Computability.VPVNP.Compression RAM.PhysicalPinsExpr RAM.MotifRows
open scoped BigOperators

variable {B : Type} {N d t : ℕ}
abbrev Live (B : Type) (d t : ℕ) := (B × Fin d) × BitWord t

def slotRow (number : B ≃ Fin N) (p : B × Fin d) := (number p.1).val*d+p.2.val
def edgeNumber (number : B ≃ Fin N) (e : Live B d t) := slotRow number e.1*2^t+(tagOrdinal t e.2).val
def siteNumber (number : B ≃ Fin N) (u : B × BitWord t) := (number u.1).val*2^t+(tagOrdinal t u.2).val

def halfSlot (j : Fin (2*d)) : Fin d := ⟨j.val%d,Nat.mod_lt _ (by have := j.isLt; omega)⟩

/-- The incoming edge is always spelled in outgoing physical coordinates. -/
def sourceHalf (G : LiftedSlots B d (BitWord t)) (u : B × BitWord t) (j : Fin (2*d)) : Live B d t :=
  let outgoing : Live B d t := ((u.1,halfSlot j),u.2)
  if j.val<d then outgoing else G.actualTarget.symm outgoing

def prefixValue (G : LiftedSlots B d (BitWord t)) (width : Live B d t → ℕ)
    (u : B × BitWord t) (j : Fin (2*d)) := ∑ i : Fin (2*d), if i.val<j.val then width (sourceHalf G u i) else 0

structure Layout where
  lanes : ℕ
  graph : ℕ
  rows : ℕ
  widths : ℕ

def HalfColumns.layout (q : HalfColumns) (eval : F → ℕ) : Layout :=
  ⟨eval q.remaining,eval q.nextGraph,eval q.nextSlots,eval q.nextWidths⟩

structure Stored (G : LiftedSlots B d (BitWord t)) (number : B ≃ Fin N) (q : Layout) (mem : ℕ → ℕ)
    (width : Live B d t → ℕ) : Prop where
  lanes : q.lanes=2^t
  srcBase : ∀ p, mem (q.graph+q.rows*3+slotRow number p)=(number (G.base.target.symm p).1).val
  srcSlot : ∀ p, mem (q.graph+q.rows*4+slotRow number p)=(G.base.target.symm p).2.val
  disp : ∀ p, mem (q.graph+q.rows*5+slotRow number p)=(tagOrdinal t (G.displacement (G.base.target.symm p))).val
  widthWord : ∀ e, mem (q.widths+edgeNumber number e)=width e

private theorem unpair (i : ℕ) {n : ℕ} (j : Fin n) :
    (i*n+j.val)/n=i ∧ (i*n+j.val)%n=j.val := by
  constructor
  · rw [Nat.mul_comm i,Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · rw [Nat.mul_comm i,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]

private theorem sub_lane (l r : BitWord t) :
    (tagOrdinal t (l-r)).val=(tagOrdinal t l).val ^^^ (tagOrdinal t r).val := by
  have neg : -r=r := by funext i; exact (by decide : ∀ z : Fin 2, -z=z) (r i)
  rw [sub_eq_add_neg,neg,tagOrdinal_add]

def readEdge (q : Layout) (mem : ℕ → ℕ) (d site half : ℕ) : ℕ :=
  let r := site/q.lanes*d+half%d
  let col i := mem (q.graph+q.rows*i+r)
  if half<d then r*q.lanes+site%q.lanes else
    (col 3*d+col 4)*q.lanes+(site%q.lanes ^^^ col 5)

theorem physical_edge {q : Layout} {mem : ℕ → ℕ} {width : Live B d t → ℕ}
    {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N} (st : Stored G number q mem width)
    (u : B × BitWord t) (j : Fin (2*d)) :
    readEdge q mem d (siteNumber number u) j.val=edgeNumber number (sourceHalf G u j) := by
  let p := (u.1,halfSlot j)
  let l := (tagOrdinal t u.2).val
  obtain ⟨v,g⟩ := unpair (number u.1).val (tagOrdinal t u.2)
  have hrow : (number u.1).val*d+j.val%d=slotRow number p := rfl
  unfold readEdge
  rw [st.lanes]
  simp only [siteNumber,v,g,hrow]
  by_cases out : j.val<d
  · simp [sourceHalf,out,edgeNumber,p]
  · rw [ite_eq_right out,st.srcBase p,st.srcSlot p,st.disp p]
    simp [sourceHalf,out,edgeNumber,slotRow,p,sub_lane]

variable (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ)
local notation "V" => Formula.natural W data mem vs

private theorem eval_read (q : HalfColumns) (d : ℕ) (s i : F) :
    V (half q d s i).edge=readEdge (q.layout V) mem d (V s) (V i) := by
  by_cases outgoing : V i < d <;>
    simp [readEdge,half,HalfColumns.layout,Demand.formulaOps,column,Formula.natural,natOp,natTest,outgoing]

theorem half_read (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width)
    (s i : F) (u : B × BitWord t) (j : Fin (2*d)) (hs : V s=siteNumber number u) (hi : V i=j.val) :
    V (half q d s i).edge=edgeNumber number (sourceHalf G u j) ∧
    V (half q d s i).side=(if j.val<d then 0 else 1) ∧ V (half q d s i).width=width (sourceHalf G u j) := by
  have edge := (eval_read W data mem vs q d s i).trans (by rw [hs,hi,physical_edge st])
  refine ⟨edge,?_,?_⟩
  · change (if decide (V i<d) then 0 else 1)=_
    simp [hi]
  · change mem (V q.nextWidths+V (half q d s i).edge)=_
    rw [edge]; exact st.widthWord _

theorem prefix_read (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width)
    (s i : F) (u : B × BitWord t) (j : Fin (2*d)) (hs : V s=siteNumber number u) (hi : V i=j.val) :
    V («prefix» q d s i)=prefixValue G width u j := by
  rw [«prefix»,totals_value]
  simp only [←List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,id_eq,prefixValue]
  apply Finset.sum_congr rfl
  intro k _
  have hv := (half_read W data mem vs q st s (.lit k.val) u k hs rfl).2.2
  change (if decide (k.val<V i) then V (half q d s (.lit k.val)).width else 0)=_
  simp [hi,hv]

theorem record_read (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width)
    (x : F) (u : B × BitWord t) (j : Fin (2*d)) (col : Fin 4)
    (addr : V x=(siteNumber number u*(2*d)+j.val)*4+col.val) :
    V (record q d x) = (![edgeNumber number (sourceHalf G u j),if j.val<d then 0 else 1,
      width (sourceHalf G u j),prefixValue G width u j] : Fin 4 → ℕ) col := by
  let s := Formula.op .div (.op .div x (.lit 4)) (.lit (2*d))
  let i := Formula.op .mod (.op .div x (.lit 4)) (.lit (2*d))
  have a := unpair (siteNumber number u*(2*d)+j.val) col
  have b := unpair (siteNumber number u) j
  have hs : V s=siteNumber number u := by change V x/4/(2*d)=_; rw [addr,a.1,b.1]
  have hi : V i=j.val := by change V x/4%(2*d)=_; rw [addr,a.1,b.2]
  have hc : V (.op .mod x (.lit 4))=col.val := by change V x%4=_; rw [addr,a.2]
  obtain ⟨he,hb,hw⟩ := half_read W data mem vs q st s i u j hs hi
  have hp := prefix_read W data mem vs q st s i u j hs hi
  change (if decide (V (.op .mod x (.lit 4))=0) then V (half q d s i).edge else
    if decide (V (.op .mod x (.lit 4))=1) then V (half q d s i).side else
    if decide (V (.op .mod x (.lit 4))=2) then V (half q d s i).width else V («prefix» q d s i))=_
  rw [hc,he,hb,hw,hp]
  fin_cases col <;> rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

end OAI
