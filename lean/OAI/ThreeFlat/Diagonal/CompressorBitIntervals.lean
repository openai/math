import Mathlib.Data.List.Sort
import OAI.ThreeFlat.Diagonal.CompressorBitOrdinal
import OAI.ThreeFlat.Diagonal.CompressorDemandGather
import OAI.ThreeFlat.Diagonal.CompressorBitOrigins
import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.Diagonal.SlotPayload

namespace OAI
/-! # Correctness of native bounded interval selection for bit addresses -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open RAM.PhysicalPinsExpr
variable {n : ℕ} (w : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (regs : Fin n → ℕ)
local notation "V" => Formula.natural w data mem regs

/-- Every positive-width interval is handled by its own endpoint callback,
even when zero-width callbacks occur before or after it. -/
theorem locate_at (pre post : List (F n × (F n → Address n))) (len : F n)
    (resolve : F n → Address n) (atBit : F n) (k : Fin 4) (j expected : ℕ)
    (index : V atBit = (pre.map (fun p => V p.1)).sum+j) (limit : j<V len)
    (read : ∀ x : F n, V x=j → V (resolve x k)=expected) :
    V (locate (pre++(len,resolve)::post) atBit k) = expected := by
  induction pre generalizing atBit with
  | nil =>
    simp only [List.map_nil,List.sum_nil,zero_add] at index
    have lt : V atBit < V len := by simpa only [index] using limit
    simp only [List.nil_append,locate,Formula.natural,natTest,decide_eq_true_eq,ite_eq_left lt]
    exact read _ index
  | cons a tail ih =>
    rcases a with ⟨size,body⟩
    simp only [List.map_cons,List.sum_cons] at index
    have ge : ¬ V atBit < V size := by omega
    simp only [List.cons_append,locate,Formula.natural,natTest,decide_eq_true_eq,ite_eq_right ge]
    apply ih
    change V atBit - V size = _
    omega

theorem startPiece_value (total index : F n) (count : ℕ) :
    V (startPiece total count index) =
      V index * (V total / count) + min (V index) (V total % count) := by
  by_cases lt : V index < V total % count
  · simp [startPiece,Formula.natural,natOp,natTest,lt,Nat.min_eq_left (Nat.le_of_lt lt)]
  · simp [startPiece,Formula.natural,natOp,natTest,lt,Nat.min_eq_right (Nat.le_of_not_gt lt)]


theorem balanced_position (total index bit : F n) (m : ℕ) (hm : 0<m)
    (i : Fin m) (k : Fin (SlotEnergy.piece (V total) m i))
    (indexValue : V index=i.val) (bitValue : V bit=k.val) :
    V (.op .add (startPiece total m index) bit) =
      (SlotEnergy.pieceIndex (V total) m hm ⟨i,k⟩).val := by
  change V (startPiece total m index) + V bit = _
  rw [startPiece_value,SlotEnergy.pieceIndex_val,indexValue,bitValue]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast BigOperators
noncomputable section

variable {n w : ℕ} {data : Param → Word w} {mem : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data mem vs

private theorem later_zero {I : Type} (ord size : I → ℕ) (a : I) (xs : List I)
    (later : ∀ x ∈ xs, ord a < ord x) :
    (xs.map (fun x => if ord x < ord a then size x else 0)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons,List.sum_cons,ite_eq_right (later x List.mem_cons_self).asymm,
      ih (fun y hy => later y (List.mem_cons_of_mem _ hy)),Nat.zero_add]

private theorem locate_ordered_word {I : Type} (ord size : I → ℕ)
    (block : I → F n × (F n → Address n)) (a : I) (bit : ℕ) (k : Fin 4)
    (expected : Word w) (xs : List I) (atBit : F n)
    (sorted : xs.Pairwise (fun x y => ord x < ord y)) (has : a ∈ xs)
    (sizes : ∀ z ∈ xs, (V (block z).1).val = size z)
    (idx : (V atBit).val = (xs.map (fun z => if ord z < ord a then size z else 0)).sum+bit)
    (fits : bit < size a) (read : ∀ y : F n, (V y).val=bit → V ((block a).2 y k)=expected) :
    V (locate (xs.map block) atBit k) = expected := by
  induction xs generalizing atBit with
  | nil => simp at has
  | cons b xs ih =>
    rcases List.pairwise_cons.mp sorted with ⟨earlier,tail⟩
    have bs := sizes b List.mem_cons_self
    rcases List.mem_cons.mp has with eq | rest
    · subst a
      rw [List.map_cons,List.sum_cons,ite_eq_right (Nat.lt_irrefl _),later_zero ord size b xs earlier] at idx
      have actual : (V atBit).val=bit := by omega
      have lt : V atBit < V (block b).1 := by change _ < (_ : Word w).val; omega
      simp [List.map_cons,locate,Formula.value,RAM.DescriptorExpr.Comparison.test,lt]
      exact read atBit actual
    · have early := earlier a rest
      rw [List.map_cons,List.sum_cons,ite_eq_left early] at idx
      have ge : ¬V atBit < V (block b).1 := by change ¬(_ : Word w).val < _; omega
      simp [List.map_cons,locate,Formula.value,RAM.DescriptorExpr.Comparison.test,ge]
      apply ih _ tail rest (fun z hz => sizes z (List.mem_cons_of_mem _ hz))
      change (if RAM.DescriptorExpr.Comparison.test .lt (V atBit) (V (block b).1) then 0
        else BinaryOp.eval .sub (V atBit) (V (block b).1)).val = _
      simp [RAM.DescriptorExpr.Comparison.test,ge,BinaryOp.eval,Fin.sub_val_of_le (le_of_not_gt ge)]
      omega

end
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast BigOperators
noncomputable section
def rowIndices (d Q : ℕ) : List (Fin d × Fin Q) :=
  (List.finRange d).flatMap fun h => (List.finRange Q).map fun u => (h,u)

theorem rowIndices_pairwise (d Q : ℕ) :
    (rowIndices d Q).Pairwise (fun x y => x.2.val+Q*x.1.val<y.2.val+Q*y.1.val) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro h _
    apply List.pairwise_map.mpr
    exact (List.sortedLT_finRange Q).pairwise.imp fun {_ _} ab => Nat.add_lt_add_right ab _
  · apply (List.sortedLT_finRange d).pairwise.imp
    intro h k hk x hx y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
    change i.val+Q*h.val<j.val+Q*k.val
    have step : Q*(h.val+1) ≤ Q*k.val := Nat.mul_le_mul_left Q hk
    rw [Nat.mul_add,Nat.mul_one] at step
    have := i.isLt
    omega

theorem rowIndices_mem {d Q : ℕ} (z : Fin d × Fin Q) : z ∈ rowIndices d Q := by
  exact List.mem_flatMap.mpr ⟨z.1,List.mem_finRange _,List.mem_map.mpr ⟨z.2,List.mem_finRange _,rfl⟩⟩

theorem rowIndices_sum {d Q : ℕ} (f : Fin d × Fin Q → ℕ) :
    ((rowIndices d Q).map f).sum = ∑ h, ∑ u, f (h,u) := by
  have rows (l : List (Fin d)) :
      ((l.flatMap (fun h => (List.finRange Q).map fun u => (h,u))).map f).sum =
      (l.map fun h => ∑ u, f (h,u)).sum := by
    induction l with
    | nil => rfl
    | cons h l ih =>
      rw [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]
      apply congrArg (fun m => m+(l.map fun h => ∑ u, f (h,u)).sum)
      simp only [← List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq]
  simpa only [rowIndices,← List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq] using rows (List.finRange d)

variable {n w : ℕ} {data : Param → Word w} {mem : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data mem vs

theorem balanced_position_word (total index bit : F n) (b Q : ℕ) (pos : 0<Q)
    (hb : b<2^w) (hq : Q<2^w) (i : Fin Q) (j : Fin (SlotEnergy.piece b Q i))
    (ht : V total=(b:Word w)) (hi : V index=(i.val:Word w)) (hj : V bit=(j.val:Word w)) :
    (V (.op .add (startPiece total Q index) bit)).val = (SlotEnergy.pieceIndex b Q pos ⟨i,j⟩).val := by
  let q := Formula.op .div total (.lit Q)
  let r := Formula.op .mod total (.lit Q)
  have qs : V q = ((b/Q:ℕ):Word w) := by
    change BinaryOp.eval .div (V total) (Q:Word w)=_
    rw [ht]
    exact op_cast .div b Q ⟨hb,hq⟩
  have rs : V r = ((b%Q:ℕ):Word w) := by
    change BinaryOp.eval .mod (V total) (Q:Word w)=_
    rw [ht]
    exact op_cast .mod b Q ⟨hb,hq⟩
  have o : V index < V r ↔ i.val<b%Q := by
    rw [hi,rs,Fin.lt_def,Fin.val_cast_of_lt (i.isLt.trans hq),Fin.val_cast_of_lt ((Nat.mod_lt b pos).trans hq)]
  have ri : V (.select .lt index r index r) = ((min i.val (b%Q):ℕ):Word w) := by
    by_cases h : i.val < b%Q
    · simpa only [Formula.value,RAM.DescriptorExpr.Comparison.test,decide_eq_true_eq,ite_eq_left (o.mpr h),min_eq_left h.le] using hi
    · simpa only [Formula.value,RAM.DescriptorExpr.Comparison.test,decide_eq_true_eq,ite_eq_right (mt o.mp h),
        min_eq_right (Nat.le_of_not_gt h)] using rs
  have valEq : V (.op .add (startPiece total Q index) bit) = ((SlotEnergy.pieceIndex b Q pos ⟨i,j⟩).val : Word w) := by
    change (V index * V q + V (.select .lt index r index r)) + V bit = _
    rw [hi,qs,ri,hj,SlotEnergy.pieceIndex_val,Nat.cast_add,Nat.cast_add]
    have product : (i.val : Word w) * ((b / Q : ℕ) : Word w) =
        ((i.val * (b / Q) : ℕ) : Word w) := op_cast (w:=w) .mul i.val (b/Q) trivial
    exact congrArg (fun z : Word w => z + ((min i.val (b%Q) : ℕ) : Word w) + (j.val : Word w)) product
  exact (congrArg Fin.val valEq).trans (Fin.val_cast_of_lt ((SlotEnergy.pieceIndex b Q pos ⟨i,j⟩).isLt.trans hb))

def sourceInterval (ptr : F n) (S : Graph.Stage) (s : Placement.Site (F n)) (port : F n)
    (h : Fin S.degree) (u : Fin (2^S.colors)) : Ends (F n) :=
  let o := Demand.formulaOps n
  ends o (oldColumns o ptr) S.degree false ⟨s,.lit u.val,.lit h.val⟩ port

set_option Elab.async false

/-- Reading the width word for a row of the actual arc table recovers the
natural interval length, including the zero contributed by an absent arc. -/
theorem source_size_word {t l : ℕ} {B H : Type} [AddCommGroup H] [Fintype H] [Fintype B]
    (ptr : F n) (S : Graph.Stage) (site : Placement.Site (F n)) (port : F n)
    {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
    {base : B ↪ ℕ} {widths : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
    {E : Codec B w S.colors t l}
    (R : Placement.ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map
      (Formula.value data mem vs)) mem)
    (W : Demand.WidthReads P E base data mem vs (layout ptr S).table
      (layout ptr S).tagCount (layout ptr S).laneCount widths)
    (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S.degree)
    (hs : site.map (Formula.value data mem vs)=siteCode E p.1)
    (hp : Formula.value data mem vs port=(p.2.val : Word w))
    (widthFit : ∀ a,widths a < 2^w) (h : Fin S.degree) (u : Fin (2^S.colors)) :
    (Formula.value data mem vs
      (Demand.element (oldColumns (Demand.formulaOps n) ptr) (layout ptr S) site port h u)).val =
        gatherElements P widths p h u :=by
  have fit : gatherElements P widths p h u < 2^w := by
    let position := ((tagOrdinal S.colors).symm u,P.slotLabel.symm h)
    change (if ttAt P p position then widths (p,position) else 0) < 2^w
    split
    · exact widthFit (p,position)
    · exact Nat.two_pow_pos w
  have raw := Demand.element_code (g:=oldColumns (Demand.formulaOps n) ptr)
    (table:=(layout ptr S).table) (tagCount:=(layout ptr S).tagCount)
    (laneCount:=(layout ptr S).laneCount) R W p site port h u hs hp
  exact (congrArg Fin.val raw).trans (Fin.val_cast_of_lt fit)


variable {t l : ℕ} {B H : Type} [AddCommGroup H] [Fintype H] [Fintype B]
variable (ptr : F n) (S : Graph.Stage) (lay : Bool)
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {base : B ↪ ℕ} {widths : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
variable {E : Codec B w S.colors t l} (site : Placement.Site (F n)) (port party : F n)
variable (R : Placement.ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map
  (Formula.value data mem vs)) mem)
variable (W : Demand.WidthReads P E base data mem vs (layout ptr S).table
  (layout ptr S).tagCount (layout ptr S).laneCount widths)

private theorem thickBlocks_rows :
    thickBlocks ptr S lay site port party =
      (rowIndices S.degree (2^S.colors)).map (fun x =>
        (Demand.element (oldColumns (Demand.formulaOps n) ptr) (layout ptr S) site port x.1 x.2,
          oldHalf ptr S lay (sourceInterval ptr S site port x.1 x.2) party)) := by
  simp only [thickBlocks,rowIndices,sourceInterval,List.map_flatMap,List.map_map]; rfl

open scoped Fin.CommRing
include R W

/-- The selected native TT interval is the original physical arc containing the
bit in the ordered AB payload, with its exact offset inside that arc. -/
theorem thickBlocks_oldBit_word (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S.degree)
    (hs : site.map (Formula.value data mem vs)=siteCode E p.1) (hp : (Formula.value data mem vs) port=(p.2.val : Word w))
    (widthFit : ∀ a,widths a<2^w) (a : ThickAt P p) (bit : Fin (widths a.val)) (atBit : F n)
    (idx : ((Formula.value data mem vs) atBit).val = (oldBit P (Demand.key P base) widths p ⟨a,bit⟩).val)
    (k : Fin 4) (expected : Word w)
    (read : ∀ j : F n, ((Formula.value data mem vs) j).val = bit.val →
      (Formula.value data mem vs) (oldHalf ptr S lay
        (sourceInterval ptr S site port (P.slotLabel a.val.2.2) (tagOrdinal S.colors a.val.2.1)) party j k)=expected) :
    (Formula.value data mem vs) (locate (thickBlocks ptr S lay site port party) atBit k)=expected := by
  let I := Fin S.degree × Fin (2^S.colors)
  let all := rowIndices S.degree (2^S.colors)
  let z : I := (P.slotLabel a.val.2.2,tagOrdinal S.colors a.val.2.1)
  let ord (x : I) := x.2.val + 2^S.colors*x.1.val
  let len (x : I) := gatherElements P widths p x.1 x.2
  let blk (x : I) : F n × (F n → Address n) :=
    (Demand.element (oldColumns (Demand.formulaOps n) ptr) (layout ptr S) site port x.1 x.2,oldHalf ptr S lay (sourceInterval ptr S site port x.1 x.2) party)
  have rows : thickBlocks ptr S lay site port party = all.map blk :=
    thickBlocks_rows ptr S lay site port party
  have sizes (x : I) : ((Formula.value data mem vs) (blk x).1).val = len x :=
    source_size_word ptr S site port R W p hs hp widthFit x.1 x.2
  have source : (p,a.val.2) = a.val := Prod.ext a.property.1.symm rfl
  have flags : ttAt P p a.val.2 := (thickFiber P p a).property
  have sz : len z=widths a.val := by
    dsimp only [len,gatherElements,z]
    simp only [Equiv.symm_apply_apply,Prod.mk.eta,ite_eq_left flags,source]
  have position : ((Formula.value data mem vs) atBit).val =
      (all.map (fun x => if ord x < ord z then len x else 0)).sum+bit.val := by
    rw [idx,show (all.map (fun x => if ord x < ord z then len x else 0)).sum = _ from
      rowIndices_sum (fun x : I => if ord x < ord z then len x else 0)]
    exact oldBit_position P base (tagOrdinal t).toEmbedding (tagOrdinal l).toEmbedding widths p a bit
  rw [rows]
  exact locate_ordered_word ord len blk z bit.val k expected all atBit (rowIndices_pairwise _ _)
    (rowIndices_mem z) (fun x _ => sizes x) position (bit.isLt.trans_eq sz.symm) read

/-- An occupied AB piece bit of the actual demand assignment, gathered by
the native variable-width scan and then read from its old half wire. -/
theorem thickBlocks_piece_word (p : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) × Fin S.degree)
    (hs : site.map (Formula.value data mem vs)=siteCode E p.1) (hp : (Formula.value data mem vs) port=(p.2.val : Word w))
    (widthFit : ∀ a,widths a<2^w) (Q : ℕ) (pos : 0<Q) (i : Fin Q)
    (j : Fin (SlotEnergy.piece (CompressorPacking.thickWidth P widths p) Q i))
    (total rank bit : F n) (totalFit : CompressorPacking.thickWidth P widths p < 2^w) (qFit : Q<2^w)
    (ht : (Formula.value data mem vs) total=(CompressorPacking.thickWidth P widths p:Word w)) (hr : (Formula.value data mem vs) rank=(i.val:Word w))
    (hj : (Formula.value data mem vs) bit=(j.val:Word w)) (k : Fin 4) (expected : Word w) :
    let chosen := (oldBit P (Demand.key P base) widths p).symm
      (SlotEnergy.pieceIndex (CompressorPacking.thickWidth P widths p) Q pos ⟨i,j⟩)
    (∀ y : F n, ((Formula.value data mem vs) y).val = chosen.2.val → (Formula.value data mem vs) (oldHalf ptr S lay
      (sourceInterval ptr S site port (P.slotLabel chosen.1.val.2.2)
        (tagOrdinal S.colors chosen.1.val.2.1)) party y k)=expected) →
    (Formula.value data mem vs) (locate (thickBlocks ptr S lay site port party) (.op .add (startPiece total Q rank) bit) k)=expected := by
  intro chosen read
  apply thickBlocks_oldBit_word ptr S lay site port party R W p hs hp widthFit chosen.1 chosen.2 _ _ k expected read
  simpa only [chosen,Sigma.eta,Equiv.apply_symm_apply] using
    balanced_position_word total rank bit _ Q pos totalFit qFit i j ht hr hj


end
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
