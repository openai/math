import OAI.Computability.BorderVNP.CellPacketGeometryArrays
import OAI.Computability.BorderVNP.CellPacketGeometrySiteTail

/-! # Global descriptor ordinals of the sparse cell packet

The two word ordinals of each public chunk come from its typed public span. Private
boxes name their original delivery operand. Stable filtering recovers the actual
canonical schedule and the three reserved descriptors in every cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
open CellSparse.Packet.Source (Part Box boxPart plan)
open BorderVNP.CellPacketGeometry
open private filter_one from OAI.Computability.BorderVNP.CellPacketGeometrySiteWords

variable {C : ℕ} {S Orig E : Type}

/-- First and last raw public ordinal of a typed span. -/
def Span.reference {raw : List (Fin C × ℕ)} {c : Fin C} {pos size : ℕ}
    (sp : Span raw c pos size) : Reference raw.length E :=
  .words sp.first.ordinal sp.last.ordinal

/-- Row-major reference for the box at one actual site and box index. -/
def Directory.boxReference (D : Directory S Orig C) (pin : Orig → E)
    (i : Fin D.sites.length) (j : Fin (D.boxes D.sites[i.val]).length) : Reference D.words.length E :=
  match h : (D.boxes D.sites[i.val])[j.val] with
  | .inl fs => (D.boxSpan i j fs h).reference
  | .inr a => .site (pin a)

/-- Descriptor source rows for one site's boxes, before any cell selection. -/
def Directory.siteReferences (D : Directory S Orig C) (pin : Orig → E) (i : Fin D.sites.length) :=
  List.ofFn (D.boxReference pin i)

/-- The complete second-sort source directory, including the reserved descriptor
triples following the static final chunk of each cell. -/
def Directory.referenceRows (D : Directory S Orig C) (pin : Orig → E) :
    List (Fin C × Reference D.words.length E) :=
  (List.ofFn fun c : Fin C => (c,(D.headerSpan c).reference)) ++
    (List.ofFn fun i : Fin D.sites.length =>
      (D.siteReferences pin i).map (Prod.mk (D.owner D.sites[i.val]))).flatten ++
    (List.ofFn fun c : Fin C => [(c,(D.tailSpan c).reference),(c,.blank),(c,.blank),(c,.blank)]).flatten

private def keep {α : Type*} (c : Fin C) (xs : List (Fin C × α)) : List α :=
  (xs.filter fun x => decide (x.1 = c)).map Prod.snd

private theorem keep_tag {α : Type*} (c a : Fin C) (xs : List α) :
    keep c (xs.map (Prod.mk a)) = if a = c then xs else [] := by
  induction xs with
  | nil => simp [keep]
  | cons x xs ih =>
    by_cases h : a=c <;> simp [keep,h] at ih ⊢
    exact ih

private theorem keep_append {α : Type*} (c : Fin C) (xs ys : List (Fin C × α)) :
    keep c (xs++ys) = keep c xs ++ keep c ys := by simp [keep]

private theorem keep_groups {α β : Type*} (c : Fin C) (xs : List β) (f : β → List (Fin C × α)) :
    keep c (xs.flatMap f) = xs.flatMap (fun i => keep c (f i)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,keep_append,ih]

private theorem flat_ofFn {α : Type*} {n : ℕ} (f : Fin n → List α) :
    (List.ofFn f).flatten = (List.finRange n).flatMap f := by
  simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]

private theorem singleton_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn (fun i => [f i])).flatten = List.ofFn f := by
  rw [flat_ofFn,← List.map_eq_flatMap]
  simp only [List.finRange,List.map_ofFn,Function.comp_def]

private theorem by_cell {α : Type*} (c : Fin C) (f : Fin C → List α) :
    keep c ((List.ofFn fun a : Fin C => (f a).map (Prod.mk a)).flatten) = f c := by
  rw [flat_ofFn,keep_groups]
  simp only [keep_tag]
  have h : ∀ xs : List (Fin C), xs.flatMap (fun a => if a=c then f a else []) =
      (owned c id xs).flatMap f := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => by_cases eq : a=c <;> simp [owned,eq] at ih ⊢ <;> exact ih
  rw [h]
  rw [filter_one _ _ (List.nodup_finRange C)]
  simp

/-- Native-order references of one cell, before its three local scan reservations. -/
def Directory.cellReferences (D : Directory S Orig C) (pin : Orig → E) (c : Fin C) :
    List (Reference D.words.length E) :=
  (D.headerSpan c).reference ::
    (List.ofFn fun i : Fin D.sites.length =>
      if D.owner D.sites[i.val] = c then D.siteReferences pin i else []).flatten ++
    [(D.tailSpan c).reference]

/-- Stable filtering by the evaluated owner leaves the native schedule followed
by exactly three all-zero descriptors. -/
theorem Directory.filter_referenceRows (D : Directory S Orig C) (pin : Orig → E) (c : Fin C) :
    ((D.referenceRows pin).filter (fun x => decide (x.1=c))).map Prod.snd =
      D.cellReferences pin c ++ [.blank,.blank,.blank] := by
  change keep c _ = _
  simp only [Directory.referenceRows,keep_append]
  have head := by_cell c (fun a => [(D.headerSpan a).reference (E := E)])
  have tail := by_cell c (fun a => [(D.tailSpan a).reference (E := E),.blank,.blank,.blank])
  simp only [List.map_cons,List.map_nil,singleton_ofFn] at head
  simp only [List.map_cons,List.map_nil] at tail
  rw [head,tail]
  simp only [flat_ofFn,keep_groups,keep_tag,
    Directory.cellReferences,List.cons_append,List.nil_append,List.append_assoc]

private theorem concatenate {N : ℕ} {owner : Fin N → Fin C} {c : Fin C}
    {arg : E → ℕ} {slot : Orig → ℕ} {n : ℕ} (pos : ℕ → ℕ)
    (ps : Fin n → List (Source.Part Orig)) (rs : Fin n → List (Reference N E))
    (step : ∀ i : Fin n, ∀ {p r}, Links owner c arg slot (pos (i.val+1)) p r →
      Links owner c arg slot (pos i.val) (ps i ++ p) (rs i ++ r))
    {p r} (last : Links owner c arg slot (pos n) p r) :
    Links owner c arg slot (pos 0) ((List.ofFn ps).flatten ++ p) ((List.ofFn rs).flatten ++ r) := by
  induction n generalizing pos with
  | zero => simpa using last
  | succ n ih =>
    have s := ih (fun t => pos (t+1)) (fun i => ps i.succ) (fun i => rs i.succ)
      (fun i => step i.succ) last
    simpa only [List.ofFn_succ,List.flatten_cons,List.append_assoc,Fin.val_zero] using step 0 s

private def Directory.sitePos (D : Directory S Orig C) (c : Fin C) (i : ℕ) :=
  (select c (D.headers ++ siteRows D.owner (fun s => boxWords (D.boxes s)) (D.sites.take i))).length

private theorem sitePos_succ (D : Directory S Orig C) (c : Fin C) (i : Fin D.sites.length) :
    D.sitePos c (i.val+1) = D.sitePos c i.val +
      (if D.owner D.sites[i.val] = c then boxWords (D.boxes D.sites[i.val]) else []).length := by
  unfold Directory.sitePos
  rw [List.take_succ_eq_append_getElem i.isLt]
  simp only [siteRows,List.flatMap_append,List.flatMap_singleton,select_append,select_tag,
    List.length_append,Nat.add_assoc]

private theorem boxWords_succ (xs : List (Box Orig)) (i : Fin xs.length) :
    boxWords (xs.take (i.val+1)) = boxWords (xs.take i.val) ++ (boxPart xs[i.val]).publicBuffer := by
  have h := congrArg (boxWords (Orig := Orig)) (List.take_succ_eq_append_getElem i.isLt)
  simpa only [boxWords,List.map_append,List.map_cons,List.map_nil,List.flatMap_append,List.flatMap_singleton] using h

private theorem link_site (D : Directory S Orig C) (pin : Orig → E) (arg : E → ℕ)
    (slot : Orig → ℕ) (addr : ∀ a, arg (pin a) = slot a) (c : Fin C) (i : Fin D.sites.length)
    {ps rs} (next : Links (fun z => D.words[z.val].1) c arg slot (D.sitePos c (i.val+1)) ps rs) :
    Links (fun z => D.words[z.val].1) c arg slot (D.sitePos c i.val)
      ((if D.owner D.sites[i.val]=c then (D.boxes D.sites[i.val]).map boxPart else []) ++ ps)
      ((if D.owner D.sites[i.val]=c then D.siteReferences pin i else []) ++ rs) := by
  rw [sitePos_succ] at next
  split_ifs with h
  · subst c
    let c := D.owner D.sites[i.val]
    let boxes := D.boxes D.sites[i.val]
    let pos := fun j => D.sitePos c i.val + (boxWords (boxes.take j)).length
    have last : Links (fun z => D.words[z.val].1) c arg slot (pos boxes.length) ps rs := by
      simpa [pos,boxes,c] using next
    have step (j : Fin boxes.length) {p r}
        (rest : Links (fun z => D.words[z.val].1) c arg slot (pos (j.val+1)) p r) :
        Links (fun z => D.words[z.val].1) c arg slot (pos j.val)
          ([boxPart boxes[j.val]] ++ p) ([D.boxReference pin i j] ++ r) := by
      have advance : pos (j.val+1) = pos j.val + (boxPart boxes[j.val]).publicBuffer.length := by
        simp only [pos,boxWords_succ boxes j,List.length_append,Nat.add_assoc]
      rw [advance] at rest
      cases hb : boxes[j.val] with
      | inr a =>
        rw [hb] at rest
        have br : D.boxReference pin i j = .site (pin a) := by
          unfold Directory.boxReference
          split <;> rename_i e <;> rw [show (D.boxes D.sites[i.val])[j.val] = .inr a from hb] at e <;> cases e
          rfl
        simpa [br,boxPart,Part.publicBuffer] using
          (Links.site a (pin a) (addr a) (by simpa [boxPart,Part.publicBuffer] using rest) :
            Links _ c arg slot (pos j.val) (.original a :: p) (.site (pin a) :: r))
      | inl fs =>
        rw [hb] at rest
        let sp := D.boxSpan i j fs hb
        have prior : (select c (D.headers ++ siteRows D.owner (fun s => boxWords (D.boxes s))
            (D.sites.take i.val) ++ tag c (boxWords (boxes.take j.val)))).length = pos j.val := by
          simp [pos,Directory.sitePos,Nat.add_assoc]
        have br : D.boxReference pin i j = sp.reference := by
          unfold Directory.boxReference
          split <;> rename_i e <;> rw [show (D.boxes D.sites[i.val])[j.val] = .inl fs from hb] at e <;> cases e
          rfl
        simp only [br,boxPart,List.singleton_append]
        exact prior ▸ Links.of_span sp (by simp [fieldList])
          (by rw [prior]; simpa [boxPart,Part.publicBuffer] using rest)
    have all := concatenate pos (fun j : Fin boxes.length => [boxPart boxes[j.val]])
      (fun j => [D.boxReference pin i j]) (fun j => step j) last
    simp only [singleton_ofFn,List.ofFn_getElem_eq_map] at all
    simpa [pos,boxes,boxWords,Directory.siteReferences] using all
  · simpa [h] using next

/-- Every selected reference is linked to its true native part, with the local
word offset advanced by exactly the number of public words of earlier boxes. -/
theorem Directory.links_cellReferences (D : Directory S Orig C) (pin : Orig → E) (arg : E → ℕ)
    (slot : Orig → ℕ) (addr : ∀ a, arg (pin a) = slot a) (c : Fin C) :
    Links (fun z => D.words[z.val].1) c arg slot 0
      (plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c))
      (D.cellReferences pin c) := by
  let ps := fun i : Fin D.sites.length =>
    if D.owner D.sites[i.val]=c then (D.boxes D.sites[i.val]).map boxPart else []
  let rs := fun i : Fin D.sites.length =>
    if D.owner D.sites[i.val]=c then D.siteReferences pin i else []
  have merge (sites : List S) : sites.flatMap (fun s =>
      if D.owner s = c then (D.boxes s).map boxPart else []) =
      ((owned c D.owner sites).flatMap D.boxes).map boxPart := by
    induction sites with
    | nil => rfl
    | cons s sites ih => by_cases eq : D.owner s = c <;> simp [owned,eq] at ih ⊢ <;> exact ih
  have hps : (List.ofFn ps).flatten = (D.cellBoxes c).map boxPart := by
    rw [flat_ofFn]
    have eqn := congrArg (fun ys : List S => ys.flatMap (fun s =>
      if D.owner s=c then (D.boxes s).map boxPart else [])) (List.map_get_finRange D.sites)
    apply Eq.trans _ (merge D.sites)
    simpa only [ps,List.flatMap_map,Function.comp_def,List.get_eq_getElem] using eqn
  have ht : D.sitePos c D.sites.length = D.tailStart c := by simp [Directory.sitePos,Directory.tailStart,Directory.boxRows]
  have hh : D.sitePos c 0 = 2 := by simp [Directory.sitePos,Directory.headers,select_cells,siteRows]
  let tail := fieldList record (D.cellRecords c) ++ fieldList vector (D.reports c)
  have tailLinks : Links (fun z => D.words[z.val].1) c arg slot (D.sitePos c D.sites.length)
      [.publicWords tail] [(D.tailSpan c).reference] := by
    rw [ht]
    exact Links.of_span (D.tailSpan c) (by simp [fieldList]) (.nil _)
  have boxes := concatenate (D.sitePos c) ps rs (fun i => link_site D pin arg slot addr c i) tailLinks
  rw [hh,hps] at boxes
  exact Links.of_span (xs := [D.privateWires c,(D.cellBoxes c).length]) (D.headerSpan c) (by simp) boxes

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
