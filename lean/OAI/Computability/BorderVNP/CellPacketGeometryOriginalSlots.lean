import OAI.Computability.BorderVNP.CellPacketGeometryFinalDirectory

/-! # Injecting each per-cell original site occurrence into the global source directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse Packet
variable {s C : ℕ} {Orig : Type}

/-- Original entries in global stable site and local box order, retaining the
physical final-cell label of each entry. Public paid boxes contribute no entry. -/
def Directory.originalRows (D : Directory (Fin s) Orig C) : List (Fin C × Orig) :=
  D.sites.flatMap fun i => ((D.boxes i).filterMap Sum.getRight?).map (Prod.mk (D.owner i))

/-- Stable input ordinals of the private entries read by the indicated cell. -/
def Directory.originalOrdinals (D : Directory (Fin s) Orig C) (c : Fin C) :
    List (Fin D.originalRows.length) :=
  (List.finRange D.originalRows.length).filter fun j => decide (D.originalRows[j.val].1 = c)

private theorem filter_map {U V : Type} (p : U → Bool) (f : U → V) (xs : List U) :
    (xs.filter p).map f = xs.filterMap (fun x => if p x then some (f x) else none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h,ih]

/-- Selecting the real original ordinals recovers the opaque part of the
actual per-cell box table. This includes sites at arbitrary positions in a
mixed public/private geometry roster. -/
theorem Directory.original_select (D : Directory (Fin s) Orig C) (c : Fin C) :
    (D.originalOrdinals c).map (fun j => D.originalRows[j.val].2) =
      (D.cellBoxes c).filterMap Sum.getRight? := by
  let r := D.originalRows
  let extract (ls : List (Fin C × Orig)) := ls.filterMap fun z => if z.1=c then some z.2 else none
  have canon : (D.originalOrdinals c).map (fun j => r[j.val].2) = extract r := by
    have eqn := congrArg extract (List.map_get_finRange r)
    simp only [extract,List.filterMap_map,Function.comp_def,List.get_eq_getElem] at eqn
    change ((List.finRange r.length).filter (fun i => decide (r[i.val].1=c))).map (fun j => r[j.val].2) =
      r.filterMap (fun z => if z.1=c then some z.2 else none)
    simpa only [filter_map,decide_eq_true_eq] using eqn
  rw [canon]
  unfold r Directory.originalRows Directory.cellBoxes
  generalize D.sites=xs
  induction xs with
  | nil => simp [extract,owned]
  | cons i xs ih =>
    by_cases live : D.owner i=c <;> simp [extract,owned,live,List.filterMap_map] at ih ⊢ <;> exact ih

/-- The actual globally stable ordinal of the cell-local opaque box occurrence. -/
def Directory.originalIndex (D : Directory (Fin s) Orig C)
    (z : Σ c : Fin C, Fin ((D.cellBoxes c).filterMap Sum.getRight?).length) : Fin D.originalRows.length :=
  let len : ((D.cellBoxes z.1).filterMap Sum.getRight?).length = (D.originalOrdinals z.1).length := by
    simpa only [List.length_map] using (congrArg List.length (D.original_select z.1)).symm
  (D.originalOrdinals z.1).get (z.2.cast len)

/-- A physically selected original source has both the requested cell owner
and the exact named one-copy box delivered by the private packet ABI. -/
theorem Directory.originalIndex_get (D : Directory (Fin s) Orig C)
    (z : Σ c : Fin C, Fin ((D.cellBoxes c).filterMap Sum.getRight?).length) :
    D.originalRows[(D.originalIndex z).val] = (z.1,((D.cellBoxes z.1).filterMap Sum.getRight?).get z.2) := by
  have mem : D.originalIndex z ∈ D.originalOrdinals z.1 := List.get_mem ..
  have own := of_decide_eq_true (List.mem_filter.mp mem).2
  have sz : z.2.val < (D.originalOrdinals z.1).length := by
    have eqn := congrArg List.length (D.original_select z.1)
    simp only [List.length_map] at eqn
    omega
  have hit := List.getElem_of_eq (D.original_select z.1) (by simpa using sz)
  simp only [List.getElem_map] at hit
  exact Prod.ext own hit

/-- All actual cell-local original entries inject into the flat private roster,
without any assumption of distinct numerical payloads or opaque source words. -/
def Directory.originalEmbedding (D : Directory (Fin s) Orig C) :
    (Σ c : Fin C, Fin ((D.cellBoxes c).filterMap Sum.getRight?).length) ↪ Fin D.originalRows.length where
  toFun := D.originalIndex
  inj' := by
    rintro ⟨c,i⟩ ⟨d,j⟩ eqn
    have a := D.originalIndex_get ⟨c,i⟩
    have b := D.originalIndex_get ⟨d,j⟩
    have cd : c=d := congrArg Prod.fst (a.symm.trans ((congrArg D.originalRows.get eqn).trans b))
    subst d
    have dup : (D.originalOrdinals c).Nodup := (List.nodup_finRange _).filter _
    have equal := dup.get_inj_iff.mp eqn
    have ij : i=j := Fin.ext (congrArg (fun t : Fin (D.originalOrdinals c).length => t.val) equal)
    subst j
    rfl

/-- Named entry injection into the *actual* input type, when the transmitted
original name roster is a permutation of the physical flat entry indices. -/
def Directory.deliveryEmbedding {entries : ℕ} (D : Directory (Fin s) (Fin entries) C)
    (once : (D.originalRows.map Prod.snd).Nodup) :
    (Σ c : Fin C, Fin ((D.cellBoxes c).filterMap Sum.getRight?).length) ↪ Fin entries where
  toFun z := D.originalRows[(D.originalIndex z).val].2
  inj' := by
    intro a b same
    apply D.originalEmbedding.injective
    let eqn := List.length_map (f := Prod.snd) (as := D.originalRows)
    let i := (D.originalIndex a).cast eqn.symm
    let j := (D.originalIndex b).cast eqn.symm
    have ij : (D.originalRows.map Prod.snd).get i = (D.originalRows.map Prod.snd).get j := by
      simpa [i,j,List.get_eq_getElem] using same
    exact Fin.ext (congrArg (fun t : Fin (D.originalRows.map Prod.snd).length => t.val) (once.get_inj_iff.mp ij))

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
