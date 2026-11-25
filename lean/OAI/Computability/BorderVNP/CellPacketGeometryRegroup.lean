import OAI.Computability.BorderVNP.CellPacketGeometryTotals
import OAI.Computability.BorderVNP.CellPacketGeometryFixedReferences

/-! # The true site-major directory after stable sorting the record section -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
variable {s C : ℕ} {Orig : Type} {A : Type*}

/-- Gather each chronological row piece at its real final site. Anchors occur
in increasing final site order and all other public sections retain their slots. -/
def Directory.regroup (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s) : Directory (Fin s) Orig C :=
  {D with rows := fun a => (owned a anchor D.sites).flatMap D.rows}

private theorem cell_group_counts (owner : Fin s → Fin C) (atSite : Fin s → Fin s)
    (vals : Fin s → List A) (xs : List (Fin s)) (c : Fin C) :
    (∑ a : Fin s, if owner a=c then ((owned a atSite xs).flatMap vals).length else 0) =
      ((owned c (owner ∘ atSite) xs).flatMap vals).length := by
  induction xs with
  | nil => simp [owned]
  | cons z xs ih =>
    have eqn (a : Fin s) : (if owner a=c then ((owned a atSite (z::xs)).flatMap vals).length else 0) =
        (if a=atSite z then (if owner (atSite z)=c then (vals z).length else 0) else 0) +
        (if owner a=c then ((owned a atSite xs).flatMap vals).length else 0) := by
      by_cases same : a=atSite z
      · subst a; by_cases h : owner (atSite z)=c <;> simp [owned,h]
      · simp [owned,same,Ne.symm same]
    simp only [eqn,Finset.sum_add_distrib,ih]
    by_cases h : owner (atSite z)=c <;> simp [owned,h]

/-- The regrouped directory has exactly the actual original merged number of rows
per cell. The key lookup binds each piece to the cell of its true site anchor. -/
theorem Directory.regroup_counts (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s)
    (sites : D.sites = List.finRange s) (owner : ∀ i, D.owner (anchor i) = D.owner i) (c : Fin C) :
    ((D.regroup anchor).cellRecords c).length = (D.cellRecords c).length := by
  have ow : D.owner ∘ anchor = D.owner := funext owner
  change ((owned c D.owner D.sites).flatMap (fun a => (owned a anchor D.sites).flatMap D.rows)).length = _
  rw [sites,← LiveWords.merged_length]
  unfold LiveWords.total
  rw [cell_group_counts,ow,←sites]
  rfl

/-- The source suffix and all box/header/count sections are literally preserved. -/
theorem Directory.regroup_sections (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s)
    (sites : D.sites = List.finRange s) (owner : ∀ i, D.owner (anchor i) = D.owner i) :
    (D.regroup anchor).headers = D.headers ∧ (D.regroup anchor).boxRows = D.boxRows ∧
      (D.regroup anchor).counts = D.counts ∧ (D.regroup anchor).reportRows = D.reportRows := by
  refine ⟨rfl,rfl,?_,rfl⟩
  simp only [Directory.counts,D.regroup_counts anchor sites owner]

/-- Record fields of each individual source piece in source order, labeled
with the final site that owns it and its actual final cell. -/
def Directory.recordPieces (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s) :
    List (Fin s × (Fin C × ℕ)) :=
  D.sites.flatMap fun i => (tag (D.owner i) ((D.rows i).flatMap record)).map (Prod.mk (anchor i))

/-- Erasing the site key gives exactly the original chronological word stream. -/
theorem Directory.recordPieces_words (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s) :
    (D.recordPieces anchor).map Prod.snd = D.recordRows := by
  simp [Directory.recordPieces,Directory.recordRows,siteRows,List.map_flatMap,List.map_map,Function.comp_def]

private theorem select_piece (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s) (a : Fin s)
    (owner : ∀ i, D.owner (anchor i)=D.owner i) :
    ((D.recordPieces anchor).filterMap fun z => if z.1=a then some z.2 else none) =
      tag (D.owner a) (((D.regroup anchor).rows a).flatMap record) := by
  unfold Directory.recordPieces Directory.regroup
  generalize D.sites = xs
  induction xs with
  | nil => simp [owned,tag]
  | cons i xs ih =>
    by_cases h : anchor i=a
    · have ow : D.owner i = D.owner a := (owner i).symm.trans (congrArg D.owner h)
      simp [List.filterMap_map,Function.comp_def,h,owned,tag,ow,List.flatMap_append]
      simpa [tag,owned,Function.comp_def] using ih
    · simp [List.filterMap_map,h,owned,ih]

/-- The exact site-major target of the Batcher pass, with chronological scalar
order within every site and its actual merged cell key. -/
theorem Directory.recordPieces_sorted (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s)
    (sites : D.sites = List.finRange s) (owner : ∀ i, D.owner (anchor i)=D.owner i) :
    (List.finRange s).flatMap (fun a => (D.recordPieces anchor).filterMap fun z => if z.1=a then some z.2 else none) =
      (D.regroup anchor).recordRows := by
  simp only [select_piece D anchor _ owner,Directory.recordRows,siteRows]
  change _ = D.sites.flatMap _
  rw [sites]
  rfl

/-- Both streams have the same number of scalar row words. -/
theorem Directory.regroup_record_length (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s)
    (sites : D.sites = List.finRange s) : (D.regroup anchor).recordRows.length = D.recordRows.length := by
  let vals := fun i => (D.rows i).flatMap record
  have groups := owned_sum D.sites anchor vals
  have all : ((List.finRange s).flatMap (fun a => (owned a anchor D.sites).flatMap vals)).length =
      ∑ a : Fin s, ((owned a anchor D.sites).flatMap vals).length := by
    simp [List.length_flatMap,List.sum_ofFn,←List.ofFn_eq_map]
  simp only [Directory.recordRows,siteRows_length,Directory.regroup,List.flatMap_assoc]
  change (D.sites.map (fun a => ((owned a anchor D.sites).flatMap vals).length)).sum = _
  rw [show (D.sites.map (fun a => ((owned a anchor D.sites).flatMap vals).length)).sum =
      ((List.finRange s).flatMap fun a => (owned a anchor D.sites).flatMap vals).length by simp only [List.length_flatMap]; rw [sites]]
  rw [all,groups,List.length_flatMap]

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
