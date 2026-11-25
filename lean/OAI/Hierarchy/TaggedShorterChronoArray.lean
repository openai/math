import OAI.Hierarchy.TaggedShorterChronoRow
import OAI.Hierarchy.TaggedShorterChronology
import OAI.Hierarchy.TaggedShorterHistoryScan
import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # The complete chronological array supplied to the control sort -/

noncomputable section
namespace Hierarchy.TaggedShorterChronoArray
open ThreeFlat Routing Diagonal TraceRows TraceBanks TraceWords TraceSlots
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open TaggedShorterChronology TaggedShorterChronoRow
open scoped Classical BigOperators
variable {F : Type*} {S f u w r p m n : ℕ}

abbrev Input (S f u w r : ℕ) :=
  (Fin S × Fin (w+1)) ⊕ ((Fin f × In w r) ⊕ (Fin u × Fin (w+1)))
abbrev Output (m w : ℕ) := Fin (2^m) × Fin (TaggedShorterHistoryOrder.RecordWidth (w+1))
abbrev Pin (S f u w r m : ℕ) := Input S f u w r ⊕ Output m w

def external (hw : 3≤w+1) (hp : p≤2^(w+1)) (header : ℕ → Word (w+1))
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (values : Fin u → Word (w+1)) : Input S f u w r → Bool :=
  Sum.elim (fun x => bits (header x.1.val) x.2)
    (Sum.elim (Function.uncurry (writeCpu hw hp xs)) (fun x => bits (values x.1) x.2))

inductive Origin (S f u w : ℕ)
  | init (i : Fin S) (addr : Word (w+1))
  | clock (i : Fin f) (time : Word (w+1))
  | observed (i : Fin u) (addr time : Word (w+1))
  | pad

def origin (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1)) (j : ℕ) :
    Origin S f u w :=
  if h : j<S then .init ⟨j,h⟩ ⟨j,h.trans_le hs⟩
  else if t : j-S<f+u then
    let time : Word (w+1) := ⟨j-S,t.trans_le ht⟩
    if i : j-S<f then .clock ⟨j-S,i⟩ time
    else let q : Fin u := ⟨j-S-f,by omega⟩; .observed q (addr q) time
  else .pad

def record (header : ℕ → Word (w+1)) (xs : Fin f → Row (w+1) (Snapshot w p r))
    (values : Fin u → Word (w+1)) : Origin S f u w → Option (WordRecord (w+1))
  | .init i a => some ⟨.init,a,header i.val,a,0⟩
  | .clock i t => rowWordSlot t (xs i)
  | .observed i a t => some ⟨.read,a,values i,t,0⟩
  | .pad => none

theorem record_origin (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1))
    (header : ℕ → Word (w+1)) (xs : Fin f → Row (w+1) (Snapshot w p r)) (values : Fin u → Word (w+1))
    (j : ℕ) :
    record header xs values (origin hs ht addr j) = slot S hs ht header (events xs addr values) j := by
  by_cases h : j<S
  · simp [record,origin,slot,h]
  · by_cases t : j-S<f+u
    · by_cases i : j-S<f
      · have pick : (⟨j-S,t⟩ : Fin (f+u))=(⟨j-S,i⟩ : Fin f).castAdd u := rfl
        have read : events xs addr values ⟨j-S,t⟩=rowEvent (xs ⟨j-S,i⟩) := by
          rw [pick,events,Fin.append_left]; rfl
        simp only [origin,slot,dite_eq_right h,dite_eq_left t,dite_eq_left i,record,read,wordSlot_row]
      · let q : Fin u := ⟨j-S-f,by omega⟩
        have pick : (⟨j-S,t⟩ : Fin (f+u))=q.natAdd f := by apply Fin.ext; simp [q]; omega
        have read : events xs addr values ⟨j-S,t⟩=.read (addr q) (values q) := by
          rw [pick,events,Fin.append_right]
        simp only [origin,slot,dite_eq_right h,dite_eq_left t,dite_eq_right i,record,read,eventWordSlot,q]
    · simp [record,origin,slot,h,t]

def outPin (j : Fin (2^m)) (a : Out w) : Pin S f u w r m :=
  .inr (j,TaggedShorterHistoryOrder.offset keyIndices a.1 a.2)

private def fixedSource (hw : 3≤w+1) (o : Origin S f u w) (fj : Out w) :
    Pin S f u w r m ⊕ Bool :=
  let concrete (s : Option (WordRecord (w+1))) := Sum.inr (output hw s fj)
  match o with
  | .init i a => if fj.1=6 then .inl (.inl (.inl (i,fj.2))) else concrete (some ⟨.init,a,0,a,0⟩)
  | .observed i a t => if fj.1=6 then .inl (.inl (.inr (.inr (i,fj.2)))) else concrete (some ⟨.read,a,0,t,0⟩)
  | _ => concrete none

private def yes [Zero F] [One F] (source : Out w → Pin S f u w r m ⊕ Bool) (j : Fin (2^m)) :
    BitNetwork F (Fintype.card (Pin S f u w r m)) :=
  TypedWiring.glue (fun fj : Out w => Tagged.RadixStage.pullPins
    (TypedWiring.localTable (P:=Fin 2) (fun z => if z 0=z 1 then (1:F) else 0))
    (![source fj,.inl (outPin j fj)]))
    (fun _ v => (Sum.inl v : Pin S f u w r m ⊕ Empty))

private theorem yes_eval [CommSemiring F] (source : Out w → Pin S f u w r m ⊕ Bool) (j : Fin (2^m))
    (data : Pin S f u w r m → Bool) :
    TypedWiring.value (yes (F:=F) source j) data =
      if ∀ fj, Sum.elim data id (source fj)=data (outPin j fj) then 1 else 0 := by
  rw [yes,TypedWiring.glue_value]
  simp only [Fintype.sum_unique,Sum.elim_inl,Tagged.RadixStage.pullPins_value,
    TypedWiring.localTable_value,Fintype.prod_boole,Function.comp_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]

def row [Zero F] [One F] (hw : 3≤w+1) (j : Fin (2^m)) (o : Origin S f u w) :
    BitNetwork F (Fintype.card (Pin S f u w r m)) :=
  match o with
  | .clock i t => Tagged.RadixStage.pullPins (TaggedShorterChronoRow.network hw t)
      (Sum.elim (fun b => .inl (.inl (.inr (.inl (i,b))))) (fun fj => .inl (outPin j fj)))
  | other => yes (fixedSource hw other) j

set_option maxHeartbeats 750000 in
theorem row_eval [CommSemiring F] (hw : 3≤w+1) (hp : p≤2^(w+1)) (header : ℕ → Word (w+1))
    (xs : Fin f → Row (w+1) (Snapshot w p r)) (values : Fin u → Word (w+1))
    (ys : Output m w → Bool) (j : Fin (2^m)) (o : Origin S f u w) :
    TypedWiring.value (row (F:=F) hw j o) (Sum.elim (external hw hp header xs values) ys) =
      if ∀ fj : Out w, ys (j,TaggedShorterHistoryOrder.offset keyIndices fj.1 fj.2) =
        output hw (record header xs values o) fj then 1 else 0 := by
  cases o with
  | clock i t =>
    rw [row,Tagged.RadixStage.pullPins_value]
    let aux : Out w → Bool := fun fj=>ys (j,TaggedShorterHistoryOrder.offset keyIndices fj.1 fj.2)
    have ports : Sum.elim (Sum.elim (external (S:=S) hw hp header xs values) ys) id ∘
        Sum.elim (fun b => .inl (.inl (.inr (.inl (i,b))))) (fun fj => .inl (outPin j fj)) =
        Sum.elim ((rowFormat hw hp).encode (xs i)) aux := by
      funext k
      cases k <;> rfl
    rw [ports]
    rw [TaggedShorterChronoRow.eval]
    by_cases h : aux=output hw (rowWordSlot t (xs i))
    · rw [ite_eq_left h]
      split
      · rfl
      · rename_i missing
        exact False.elim (missing (fun z=>congrFun h z))
    · rw [ite_eq_right h]
      split
      · rename_i all
        exact False.elim (h (funext all))
      · rfl
  | init i a | observed i a t | pad =>
    rw [row,yes_eval] <;> try (intro k time eq; cases eq)
    congr 1
    apply propext
    apply forall_congr'
    intro ⟨fid,b⟩
    fin_cases fid <;> simp [fixedSource,record,output,fields,external,outPin,eq_comm]

def network [Zero F] [One F] (hw : 3≤w+1) (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1))
    (addr : Fin u → Word (w+1)) : BitNetwork F (Fintype.card (Pin S f u w r m)) :=
  TypedWiring.glue (fun j : Fin (2^m) => row hw j (origin hs ht addr j.val))
    (fun _ v => (Sum.inl v : Pin S f u w r m ⊕ Empty))

private theorem all_offsets (l : List (Fin 7)) (k : Fin (TaggedShorterHistoryOrder.width n l)) :
    ∃ i j, TaggedShorterHistoryOrder.offset l i j=k := by
  induction l with
  | nil => exact Fin.elim0 k
  | cons head tail ih =>
    induction k using Fin.addCases with
    | left b =>
      obtain ⟨i,j,eq⟩ := ih b
      refine ⟨i.succ,j,?_⟩
      change (TaggedShorterHistoryOrder.offset tail i j).castAdd n=b.castAdd n
      exact congrArg (Fin.castAdd n) eq
    | right j => exact ⟨0,j,rfl⟩

theorem eval [CommSemiring F] (hw : 3≤w+1) (hp : p≤2^(w+1)) (hs : S≤2^(w+1))
    (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1))
    (header : ℕ → Word (w+1)) (xs : Fin f → Row (w+1) (Snapshot w p r)) (values : Fin u → Word (w+1))
    (ys : Output m w → Bool) :
    TypedWiring.value (network (F:=F) hw hs ht addr) (Sum.elim (external hw hp header xs values) ys) =
      if ys=Function.uncurry (TaggedShorterHistoryOrder.bits (by omega) ∘
        (fun j : Fin (2^m) => slot S hs ht header (events xs addr values) j.val)) then 1 else 0 := by
  rw [network,TypedWiring.glue_value]
  simp only [Fintype.sum_unique,Sum.elim_inl,row_eval,Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext ⟨j,k⟩
    obtain ⟨fid,b,rfl⟩ := all_offsets keyIndices k
    have read := h j (fid,b)
    simp only [record_origin,output] at read
    exact read.trans (TaggedShorterHistoryOrder.field_at _ _ fid b).symm
  · rintro rfl j ⟨fid,b⟩
    rw [record_origin]
    exact TaggedShorterHistoryOrder.field_at _ _ fid b

end Hierarchy.TaggedShorterChronoArray

end
end OAI
