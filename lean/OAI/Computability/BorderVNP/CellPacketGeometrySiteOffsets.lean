import OAI.Computability.BorderVNP.CellPacketGeometrySiteWords

/-! # Stable source ordinals for the public parts of a sparse cell packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
open CellSparse.Packet.Source (Box boxPart)

variable {C : ℕ} {S Orig : Type}

/-- A source ordinal accompanied by its cell tag and count of preceding local words.
The inverse stable sorting permutation sends this ordinal to the corresponding offset
in the cell's compact word interval. -/
structure Position (raw : List (Fin C × ℕ)) (c : Fin C) (prior : ℕ) where
  /-- Global ordinal in the unsorted public stream. -/
  ordinal : Fin raw.length
  /-- The row is routed to the stated cell. -/
  owner : raw[ordinal.val].1 = c
  /-- Earlier words of this cell count its local offset. -/
  rank : (select c (raw.take ordinal.val)).length = prior

/-- A public chunk, with the first and last word of its local interval selected
by their original source ordinals. -/
structure Span (raw : List (Fin C × ℕ)) (c : Fin C) (prior size : ℕ) where
  /-- First word at local offset `prior`. -/
  first : Position raw c prior
  /-- Last word at local offset `prior+size-1`. -/
  last : Position raw c (prior+size-1)

/-- Index one word of a contiguous raw group. Its local index adds the count of
earlier words with the same cell tag. -/
def position {raw : List (Fin C × ℕ)} (c : Fin C) (pre : List (Fin C × ℕ))
    (xs : List ℕ) (post : List (Fin C × ℕ)) (split : raw = pre++tag c xs++post)
    (i : Fin xs.length) : Position raw c ((select c pre).length+i.val) := by
  subst raw
  have ht : (tag c xs).length = xs.length := by simp [tag]
  let k : Fin (pre++tag c xs++post).length := ⟨pre.length+i.val,by simp only [List.length_append,ht]; have := i.isLt; omega⟩
  refine ⟨k,?_,?_⟩
  · have bound : pre.length+i.val < (pre++tag c xs).length := by
      simp only [List.length_append,ht]; have := i.isLt; omega
    change (((pre++tag c xs)++post)[pre.length+i.val]'(by simp only [List.length_append,ht]; have := i.isLt; omega)).1 = c
    simp only [List.getElem_append_left bound,List.getElem_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    simp [tag]
  · have upper : pre.length+i.val ≤ (pre++tag c xs).length := by simp only [List.length_append,ht]; have := i.isLt; omega
    have eq : (pre++tag c xs++post).take (pre.length+i.val) = pre++tag c (xs.take i.val) := by
      rw [List.take_append_of_le_length upper,List.take_append]
      simp [tag]
    change (select c ((pre++tag c xs++post).take (pre.length+i.val))).length = _
    rw [eq,select_append,select_tag]
    simp

/-- The two stable source ordinals for any nonempty contiguous public group. -/
def span {raw : List (Fin C × ℕ)} (c : Fin C) (pre : List (Fin C × ℕ))
    (xs : List ℕ) (post : List (Fin C × ℕ)) (split : raw = pre++tag c xs++post)
    (nonempty : 0 < xs.length) : Span raw c (select c pre).length xs.length := by
  refine ⟨?_,?_⟩
  · simpa only [Nat.add_zero] using position c pre xs post split ⟨0,nonempty⟩
  · have eq : (select c pre).length+(xs.length-1) = (select c pre).length+xs.length-1 := by omega
    simpa only [eq] using position c pre xs post split ⟨xs.length-1,by omega⟩

/-- All site blocks preceding and following a selected original source index. -/
theorem siteRows_split (owner : S → Fin C) (emit : S → List ℕ) (ss : List S) (i : Fin ss.length) :
    siteRows owner emit ss = siteRows owner emit (ss.take i.val) ++
      tag (owner ss[i.val]) (emit ss[i.val]) ++ siteRows owner emit (ss.drop (i.val+1)) := by
  have h := congrArg (siteRows owner emit) (List.take_append_drop i.val ss)
  rw [List.drop_eq_getElem_cons i.isLt] at h
  simpa only [siteRows,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h.symm

private theorem finRange_split (emit : Fin C → List ℕ) (c : Fin C) :
    cellRows emit = siteRows id emit ((List.finRange C).take c.val) ++ tag c (emit c) ++
      siteRows id emit ((List.finRange C).drop (c.val+1)) := by
  simpa [cellRows] using siteRows_split id emit (List.finRange C) ⟨c.val,by simp⟩

/-- Earlier scalar sections of other cells have zero contribution to this cell. -/
theorem cell_prefix_empty (emit : Fin C → List ℕ) (c : Fin C) :
    select c (siteRows id emit ((List.finRange C).take c.val)) = [] := by
  rw [select_sites]
  have eq : owned c id ((List.finRange C).take c.val) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [id_eq,decide_eq_true_eq]
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hx
    have less : j < c.val := by simpa [List.length_take,Nat.min_eq_left c.isLt.le] using hj
    have val : x.val = j := by rw [←he]; simp
    exact fun same => less.ne (val.symm.trans (congrArg Fin.val same))
  rw [eq]; rfl

/-- Positions of the two initial words, independent of all original box lengths. -/
def Directory.headerSpan (D : Directory S Orig C) (c : Fin C) : Span D.words c 0 2 := by
  let emit := fun a : Fin C => [D.privateWires a,(D.cellBoxes a).length]
  let pre := siteRows id emit ((List.finRange C).take c.val)
  let post := siteRows id emit ((List.finRange C).drop (c.val+1)) ++ D.boxRows ++ D.counts ++ D.recordRows ++ D.reportRows
  have split : D.words = pre++tag c (emit c)++post := by
    simp only [Directory.words,Directory.headers,finRange_split emit c,pre,post,emit,List.append_assoc]
  have empty : (select c pre).length = 0 := by rw [cell_prefix_empty]; rfl
  exact empty ▸ span c pre (emit c) post split (by simp [emit])

/-- The source ordinal of a known box is obtained by summing only the public words
of earlier source sites and earlier boxes of this site. Original opaque boxes emit zero
public words and are addressed directly at their delivery slot. -/
def Directory.boxSpan (D : Directory S Orig C) (i : Fin D.sites.length)
    (j : Fin (D.boxes D.sites[i.val]).length) (fs : List Factor)
    (publicBox : (D.boxes D.sites[i.val])[j.val] = Sum.inl fs) :
    let c := D.owner D.sites[i.val]
    let pre := D.headers ++ siteRows D.owner (fun s => boxWords (D.boxes s)) (D.sites.take i.val) ++
      tag c (boxWords ((D.boxes D.sites[i.val]).take j.val))
    Span D.words c (select c pre).length (fieldList factor fs).length := by
  intro c pre
  let boxes := D.boxes D.sites[i.val]
  let xs := fieldList factor fs
  let post := tag c (boxWords (boxes.drop (j.val+1))) ++
    siteRows D.owner (fun s => boxWords (D.boxes s)) (D.sites.drop (i.val+1)) ++ D.counts ++ D.recordRows ++ D.reportRows
  have bs : boxWords boxes = boxWords (boxes.take j.val) ++ xs ++ boxWords (boxes.drop (j.val+1)) := by
    conv_lhs => rw [←List.take_append_drop j.val boxes,List.drop_eq_getElem_cons j.isLt]
    rw [show boxes[j.val] = Sum.inl fs from publicBox]
    simp [boxWords,boxPart,CellSparse.Packet.Source.Part.publicBuffer,xs,boxes,List.append_assoc]
  have split : D.words = pre++tag c xs++post := by
    rw [Directory.words,Directory.boxRows,siteRows_split _ _ _ i,bs]
    simp [pre,post,tag,c,boxes,List.append_assoc]
  exact span c pre xs post split (by simp [xs,fieldList])

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
