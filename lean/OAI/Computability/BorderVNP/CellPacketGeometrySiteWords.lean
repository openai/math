import OAI.Computability.BorderVNP.CellPacketSources

/-! # Public site and cell words in their stable geometry order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
open CellSparse.Packet.Source (Box Part boxPart plan)

variable {C : ℕ} {S Orig : Type}

/-- Annotate each public word by its cell owner before stable geometry sorting. -/
def tag (c : Fin C) (xs : List ℕ) : List (Fin C × ℕ) := xs.map (Prod.mk c)

/-- Extract one cell's public words, preserving raw ordinal order. -/
def select (c : Fin C) (rows : List (Fin C × ℕ)) : List ℕ :=
  rows.filterMap fun r => if r.1 = c then some r.2 else none

@[simp] theorem select_append (c : Fin C) (xs ys : List (Fin C × ℕ)) :
    select c (xs++ys) = select c xs ++ select c ys := List.filterMap_append

@[simp] theorem select_tag (c a : Fin C) (xs : List ℕ) :
    select c (tag a xs) = if a=c then xs else [] := by
  induction xs with
  | nil => simp [select,tag]
  | cons x xs ih =>
    by_cases h : a=c <;> simp [select,tag,h] at ih ⊢

/-- One list of consecutive geometry words per site, assigned to its selected cell. -/
def siteRows (owner : S → Fin C) (emit : S → List ℕ) (sites : List S) : List (Fin C × ℕ) :=
  sites.flatMap fun s => tag (owner s) (emit s)

/-- Keep exactly the sites of this cell in their original order. -/
def owned (c : Fin C) (owner : S → Fin C) (sites : List S) := sites.filter fun s => decide (owner s = c)

/-- Filtering the native geometry source restricts the underlying site list. -/
theorem select_sites (c : Fin C) (owner : S → Fin C) (emit : S → List ℕ) (sites : List S) :
    select c (siteRows owner emit sites) = (owned c owner sites).flatMap emit := by
  induction sites with
  | nil => rfl
  | cons s sites ih =>
    change select c (tag (owner s) (emit s) ++ siteRows owner emit sites) = _
    rw [select_append,select_tag,ih]
    by_cases hs : owner s = c <;> simp [owned,hs]

/-- One public field sequence per geometric cell. -/
def cellRows (emit : Fin C → List ℕ) := siteRows id emit (List.finRange C)

private theorem filter_one (c : Fin C) (xs : List (Fin C)) (nodup : xs.Nodup) :
    owned c id xs = if c ∈ xs then [c] else [] := by
  induction xs with
  | nil => simp [owned]
  | cons a xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nodup
    have tail := ih rest
    simp only [owned,id_eq] at tail ⊢
    by_cases same : a=c
    · subst a; simp [tail,fresh]
    · simp [same,Ne.symm same,tail]

/-- The public section for a named cell occurs exactly once. -/
theorem select_cells (c : Fin C) (emit : Fin C → List ℕ) :
    select c (cellRows emit) = emit c := by
  rw [cellRows,select_sites,filter_one _ _ (List.nodup_finRange C)]
  simp

/-- A public known box contributes its factor count and compact factors. Opaque
original boxes contribute a private delivery descriptor and zero public words. -/
def boxWords (boxes : List (Box Orig)) : List ℕ :=
  (boxes.map boxPart).flatMap CellSparse.Packet.Source.Part.publicBuffer

private theorem boxWords_append (xs ys : List (Box Orig)) :
    boxWords (xs++ys) = boxWords xs ++ boxWords ys := by simp [boxWords]

private theorem boxWords_flatMap (box : S → List (Box Orig)) (xs : List S) :
    boxWords (xs.flatMap box) = xs.flatMap fun s => boxWords (box s) := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp only [List.flatMap_cons,boxWords_append,ih]

/-- The stable public streams are emitted by cell headers, original-site boxes,
cell row counts, original-site records and cell reports, in this order. -/
structure Directory (S Orig : Type) (C : ℕ) where
  /-- Original sites in the geometry source order. -/
  sites : List S
  /-- Current cell of each original site. -/
  owner : S → Fin C
  /-- Known public boxes and delivered opaque boxes at the site. -/
  boxes : S → List (Box Orig)
  /-- Compact public row records emitted by the site. -/
  rows : S → List Record
  /-- Private assignment bank length of each cell. -/
  privateWires : Fin C → ℕ
  /-- Multiplicity address vectors reported by each cell. -/
  reports : Fin C → List (List ℕ)

/-- Merged box ordinal list for the selected cell. -/
def Directory.cellBoxes (D : Directory S Orig C) (c : Fin C) :=
  (owned c D.owner D.sites).flatMap D.boxes

/-- Merged row list, in exactly the original geometry site order. -/
def Directory.cellRecords (D : Directory S Orig C) (c : Fin C) :=
  (owned c D.owner D.sites).flatMap D.rows

/-- Two scalar header words per cell. -/
def Directory.headers (D : Directory S Orig C) :=
  cellRows fun c => [D.privateWires c,(D.cellBoxes c).length]

/-- Public portion of the original box records. -/
def Directory.boxRows (D : Directory S Orig C) :=
  siteRows D.owner (fun s => boxWords (D.boxes s)) D.sites

/-- The leading count for each merged cell record list. -/
def Directory.counts (D : Directory S Orig C) :=
  cellRows fun c => [(D.cellRecords c).length]

/-- Actual per-site sparse row words, with no repeated merged-list count. -/
def Directory.recordRows (D : Directory S Orig C) :=
  siteRows D.owner (fun s => (D.rows s).flatMap record) D.sites

/-- Cell report count followed by the public report address vectors. -/
def Directory.reportRows (D : Directory S Orig C) :=
  cellRows fun c => fieldList vector (D.reports c)

/-- Public geometry word payload in fixed raw ordinal order. -/
def Directory.words (D : Directory S Orig C) :=
  D.headers ++ D.boxRows ++ D.counts ++ D.recordRows ++ D.reportRows

/-- Stable sorting by cell extracts exactly the natural-word input of the canonical
sparse packet, including its merged lengths, without any private site table. -/
theorem Directory.select_words (D : Directory S Orig C) (c : Fin C) :
    select c D.words = (plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c)
      (D.reports c)).flatMap CellSparse.Packet.Source.Part.publicBuffer := by
  simp only [Directory.words,Directory.headers,Directory.boxRows,Directory.counts,Directory.recordRows,
    Directory.reportRows,select_append,select_cells,select_sites,plan,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,List.append_nil,CellSparse.Packet.Source.Part.publicBuffer]
  change [_,_] ++ _ ++ [_] ++ _ ++ _ = [_,_] ++ (boxWords _ ++ _)
  rw [Directory.cellBoxes,boxWords_flatMap]
  simp [Directory.cellRecords,List.flatMap_assoc,fieldList]

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
