import OAI.Computability.BorderVNP.CellPacketGeometrySchema
import OAI.Computability.BorderVNP.CellPacketGeometryExecute
import OAI.Computability.BorderVNP.CellPacketGeometrySiteOffsets

/-! # Canonical public and descriptor subsequences of a physical sort return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort Packing.Word RoutingISA.CellPacket

variable {C N p d k w M : ℕ} {E S Orig : Type}

private theorem get_filter {α β : Type*} (xs : List α) (keep : α → Bool) (v : α → β) :
    (((List.finRange xs.length).filter (fun i => keep xs[i.val])).map (fun i => v xs[i.val])) =
      (xs.filter keep).map v := by
  have h := congrArg (fun ys : List α => (ys.filter keep).map v) (List.map_get_finRange xs)
  simpa only [List.filter_map,List.map_map,Function.comp_def,List.get_eq_getElem] using h

private theorem select_eq (rows : List (Fin C × ℕ)) (c : Fin C) :
    (rows.filter (fun r => decide (r.1=c))).map Prod.snd = SiteWords.select c rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih => by_cases h : r.1=c <;> simp [SiteWords.select,h] at ih ⊢ <;> exact ih

/-- The sorted word section of the typed public shape is precisely the public
portion of the private macro packet for this cell. -/
theorem publicArray (D : SiteWords.Directory S Orig C) (fit : C+D.words.length+C ≤ 2^p) (c : Fin C) :
    let owner := fun i : Fin D.words.length => D.words[i.val].1
    let payload := fun i : Fin D.words.length => D.words[i.val].2
    (inside (fun i => Markers.key owner (Markers.row C D.words.length i.val))
      (Markers.start fit c) (Markers.stop fit c)).map
      (fun i => Markers.word payload (Markers.row C D.words.length i.val)) =
    (CellSparse.Packet.Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).flatMap
      CellSparse.Packet.Source.Part.publicBuffer := by
  intro owner payload
  rw [Markers.inside_words]
  exact (get_filter D.words _ Prod.snd).trans ((select_eq D.words c).trans (D.select_words c))

/-- The weighted source-array prefix computed from raw ordinals is exactly the
rank used by a typed span in the public shape. -/
theorem select_prefix (xs : List (Fin C × ℕ)) (c : Fin C) (i : Fin xs.length) :
    (((List.finRange xs.length).take i.val).filter (fun j => decide (xs[j.val].1=c))).length =
      (SiteWords.select c (xs.take i.val)).length := by
  rw [← select_eq,List.length_map]
  have eqn := congrArg (fun ys : List (Fin C × ℕ) => ((ys.take i.val).filter (fun r => decide (r.1=c))).length)
    (List.map_get_finRange xs)
  simpa only [← List.map_take,List.filter_map,List.length_map,Function.comp_def,List.get_eq_getElem] using eqn

/-- First and last public ordinals of the typed block certify the arithmetic
descriptor against the actual stable sort. -/
theorem Links.of_span {raw : List (Fin C × ℕ)} {c : Fin C} {prior : ℕ} {xs : List ℕ}
    (sp : SiteWords.Span raw c prior xs.length) (nonempty : 0 < xs.length)
    {arg : E → ℕ} {slot : Orig → ℕ} {parts : List (CellSparse.Packet.Source.Part Orig)}
    {refs : List (Reference raw.length E)}
    (rest : Links (fun i => raw[i.val].1) c arg slot (prior+xs.length) parts refs) :
    Links (fun i => raw[i.val].1) c arg slot prior (.publicWords xs :: parts)
      (.words sp.first.ordinal sp.last.ordinal :: refs) :=
  .words _ _ nonempty sp.first.owner sp.last.owner
    ((select_prefix raw c sp.first.ordinal).trans sp.first.rank)
    ((select_prefix raw c sp.last.ordinal).trans sp.last.rank) rest

private theorem coord_values (own : Fin M → Fin C) (ref : Fin M → Reference N E)
    (fit : C+N+C ≤ 2^p) (dest H : ℕ) (oper : E ⊕ Fin (2^p) → ℕ) (c : Fin C) :
    ((Schema.coords M).filter (fun r => decide (own r.1 = c))).map
      (fun r => ((ref r.1).fields fit dest H r.2).eval oper) =
    ((List.finRange M).filter (fun i => decide (own i = c))).flatMap
      (fun i => (ref i).values fit dest H oper) := by
  unfold Schema.coords
  generalize List.finRange M = xs
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases eqn : own a = c <;>
      simp [eqn,Reference.values,List.ofFn_succ,ih]


/-- Stable selection in the descriptor bank yields the three evaluated fields of every
selected chunk, including all explicitly reserved blank rows. -/
theorem descriptorSection (fit : C+N+C ≤ 2^p)
    (space : C+(Schema.coords M).length+C ≤ 2^d) (dest H : ℕ)
    (own : Fin M → Fin C) (ref : Fin M → Reference N E) (c : Fin C) (op : E ⊕ Fin (2^p) → ℕ) :
    let down := fun q : Fin (Schema.coords M).length => own ((Schema.coords M)[q.val]).1
    let key := fun i : Fin (2^d) => Markers.key down (Markers.row C (Schema.coords M).length i.val)
    let value := fun i : Fin (2^d) => (Schema.expression C d fit dest H ref i).eval op
    (inside key (Markers.start space c) (Markers.stop space c)).map value =
      (((List.finRange M).filter fun i => decide (own i=c)).map ref).flatMap (Reference.values fit dest H op) := by
  intro down key value
  let data := fun q : Fin (Schema.coords M).length =>
    let z := (Schema.coords M)[q.val]
    ((ref z.1).fields fit dest H z.2).eval op
  have hv (i) : value i = Markers.word data (Markers.row C (Schema.coords M).length i.val) := by
    dsimp only [value,Schema.expression]
    cases Markers.row C (Schema.coords M).length i.val <;> rfl
  rw [funext hv]
  rw [show key = fun i : Fin (2^d) => Markers.key down (Markers.row C (Schema.coords M).length i.val) from rfl,
    Markers.inside_words]
  have lists := get_filter (Schema.coords M) (fun z => decide (own z.1=c))
    (fun z => ((ref z.1).fields fit dest H z.2).eval op)
  rw [lists,coord_values]
  rw [List.flatMap_map]

/-- The descriptor section has no unused triples. It is the native table for
the correctly linked original and public parts, in their canonical order. -/
theorem descriptorArray {Site : Type} (fit : C+N+C ≤ 2^p)
    (space : C+(Schema.coords M).length+C ≤ 2^d) (dest H : ℕ)
    (own : Fin M → Fin C) (owner : Fin N → Fin C) (ref : Fin M → Reference N E)
    (arg : E → ℕ) (slot : Site → ℕ) (fs : Site → List CellSparse.Factor)
    (c : Fin C) (parts : List (CellSparse.Packet.Source.Part Site))
    (linked : Links owner c arg slot 0 parts (((List.finRange M).filter fun i => decide (own i=c)).map ref))
    (π : Equiv.Perm (Fin (2^p)))
    (rank : Monotone fun i => 2*Markers.key owner (Markers.row C N (π i).val)*2^p+(π i).val) :
    let down := fun q : Fin (Schema.coords M).length => own ((Schema.coords M)[q.val]).1
    let key := fun i : Fin (2^d) => Markers.key down (Markers.row C (Schema.coords M).length i.val)
    let value := fun i : Fin (2^d) => (Schema.expression C d fit dest H ref i).eval (Sum.elim arg (fun j => (π.symm j).val))
    (inside key (Markers.start space c) (Markers.stop space c)).map value =
      descriptors (CellSparse.Packet.Source.chunks slot H fs (dest+(π.symm (Markers.start fit c)).val+1) parts) := by
  exact (descriptorSection fit space dest H own ref c _).trans (by
    simpa only [Nat.add_zero] using linked.descriptors fit dest H fs π rank)

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
