import OAI.ThreeFlat.RAM.HistoryPartyTileTable
import OAI.ThreeFlat.RAM.HistoryPartyHeader
import OAI.ThreeFlat.RAM.HistoryUniversalArchive
import OAI.ThreeFlat.Diagonal.HistoryMotifBatchRows
import OAI.ThreeFlat.Diagonal.HistoryPartyTrees
import OAI.ThreeFlat.Diagonal.MotifNativeCompactors

namespace OAI
/-! # Exact dimensions and copy records of the two selected party batches -/

namespace ThreeFlat.RAM.HistoryPartySpecialization

open HistoryPartyHeader HistoryBatchTape Diagonal Diagonal.HistoryContraction
open Tree MotifOrderedCells MotifOuterTerms
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [CommRing F] [Fintype F] {r s e k b d B n ar : ℕ}

omit [Fintype F] in
theorem tileTable_at {H : Type*} (T : Tile F H e d b) (i : Fin r) :
    checkedTile T.rule T.table i = tileTable T := rfl

def kind {H : Type*} (T : Tile F H e d b) (good : (Fin (e*k) → Bool) → Prop)
    (letter : (Fin (e*k) → Bool) → Fin s) (tp : b+(e*d+e*d) ≤ ar) (sp : e*k+s ≤ ar) : Kind :=
  ⟨e,s,k,b,d,(HistoryStaticArchive.index F ar tp (tileTable T)).val,
    (HistoryStaticArchive.index F ar sp (MotifSelectorChecks.checkLut (F:=F) good letter)).val⟩

/-- Absolute addresses of the selected motif, its dyadic scratch values, the two header lanes
of each static LUT and the two shape lanes of the dyadic compactor count ROM. -/
structure Reads (A : Registers) (mem : ℕ → ℕ) (L : HistoryStaticArchive.Catalog F n ar)
    (r : ℕ) (t : Fin (B+1)) : Prop where
  copies : mem (A.incident+3)=r
  exponent : mem (A.dyadic+1)=t.val
  dyadic : mem (A.dyadic+2)=2^t.val
  lut : ∀ (i : Fin n) (lane : Fin 2),
    mem (A.lutBase+A.lutStride*i.val+lane.val)=L.page i lane.val
  counts : ∀ lane : Fin 2, mem (A.countBase+2*t.val+lane.val)=HistoryCompactorCounts.words F t lane

private theorem lutWords (A : Registers) (mem : ℕ → ℕ) (L : HistoryStaticArchive.Catalog F n ar)
    (t : Fin (B+1)) (read : Reads A mem L r t) (i : Fin n) :
    mem (A.lutBase+A.lutStride*i.val)=2^(L.arity i) ∧
    mem (A.lutBase+A.lutStride*i.val+1)=2^(L.arity i)*(L.arity i+1) := by
  constructor
  · simpa [HistoryStaticArchive.Catalog.page, HistoryStaticArchive.Catalog.rows] using read.lut i 0
  · simpa [HistoryStaticArchive.Catalog.page, HistoryStaticArchive.Catalog.rows] using read.lut i 1

private theorem compWords (A : Registers) (mem : ℕ → ℕ) (L : HistoryStaticArchive.Catalog F n ar)
    (t : Fin (B+1)) (read : Reads A mem L r t) (small : ℕ) :
    mem (A.dyadic+2)*mem (A.countBase+2*mem (A.dyadic+1)) =
        (MotifNativeCompactors.partialInput F small t.val).cells ∧
    mem (A.dyadic+2)*mem (A.countBase+2*mem (A.dyadic+1)+1) =
        (MotifNativeCompactors.partialInput F small t.val).internal := by
  have h := HistoryCompactorCounts.shape F t small
  rw [read.exponent,read.dyadic]
  have z := read.counts 0
  have o := read.counts 1
  simp only [Fin.val_zero,Nat.add_zero] at z
  change mem (A.countBase+2*t.val+1)=_ at o
  rw [z,o]
  constructor
  · simpa [MotifNativeCompactors.partialInput,Nat.mul_comm] using h.1.symm
  · simpa [MotifNativeCompactors.partialInput,Nat.mul_comm] using h.2.symm

section Party
variable {H : Type*} (T : Tile F H e d b) (good : (Fin (e*k) → Bool) → Prop)
    (letter : (Fin (e*k) → Bool) → Fin s) (tp : b+(e*d+e*d) ≤ ar) (sp : e*k+s ≤ ar)
    (A : Registers) (mem : ℕ → ℕ) (t : Fin (B+1)) (read : Reads A mem (HistoryStaticArchive.all F ar) r t)

local notation "S" => kind T good letter tp sp
local notation "SC" => MotifNativeCompactors.partialInput F r t.val
local notation "PC" => MotifNativeCompactors.partialInput F (r*d) t.val
local notation "SA" => batch A S mem true
local notation "PA" => batch A S mem false

include read in
theorem checks_fields : (SA).r=r ∧ (SA).s=s ∧ (SA).parentPins=r*(e*k) ∧ (SA).shared=r*s ∧
    (SA).left=BatchRows.lutSize (e*k+s) ∧ (SA).right=BatchRows.compSize SC := by
  have h := lutWords A mem _ t read
    (HistoryStaticArchive.index F ar sp (MotifSelectorChecks.checkLut (F:=F) good letter))
  simp only [HistoryStaticArchive.arity_index] at h
  have c := compWords A mem _ t read r
  simp only [HistoryPartyHeader.batch,kind,ite_true,read.copies]
  refine ⟨trivial,trivial,trivial,trivial,?_,?_⟩
  · simp only [BatchRows.lutSize,h.1,h.2]
  · simp only [BatchRows.compSize,c.1,c.2]
    congr 1; omega

include read in
theorem payload_fields : (PA).r=r ∧ (PA).s=e ∧ (PA).parentPins=r*b+e*(r*d) ∧ (PA).shared=2*(e*(r*d)) ∧
    (PA).left=BatchRows.lutSize (b+(e*d+e*d)) ∧ (PA).right=BatchRows.compSize PC := by
  have h := lutWords A mem _ t read (HistoryStaticArchive.index F ar tp (tileTable T))
  simp only [HistoryStaticArchive.arity_index] at h
  have c := compWords A mem _ t read (r*d)
  simp only [HistoryPartyHeader.batch,kind,Bool.false_eq_true,ite_false,read.copies]
  refine ⟨trivial,trivial,trivial,trivial,?_,?_⟩
  · simp only [BatchRows.lutSize,h.1,h.2,two_mul]
  · simp only [BatchRows.compSize,c.1,c.2]
    congr 1; omega

include read in
theorem checks_dimensions (z : Histogram (Fin s) r) :
    BatchRows.Sizes (fun i => (MotifSelectorChecks.components good letter SC z i).net)
      (SA).left (SA).right := by
  have f := checks_fields T good letter tp sp A mem t read
  rw [f.2.2.2.2.1,f.2.2.2.2.2]
  exact BatchRows.checks_sizes good letter SC z

include read in
theorem payload_dimensions :
    BatchRows.Sizes (fun i => (pieces (checkedTile T.rule T.table) PC i).N)
      (PA).left (PA).right := by
  have f := payload_fields T good letter tp sp A mem t read
  rw [f.2.2.2.2.1,f.2.2.2.2.2]
  exact BatchRows.payload_sizes _ PC

include read in
theorem checks_row (z : Histogram (Fin s) r) (i : Fin (r+s)) :
    let X := MotifSelectorChecks.components good letter SC z
    copy ⟨A.streams,A.maps,0,0⟩ (fun j => (X j).wire) (fun j => Tree.atom (X j).net) i = (SA).row i.val := by
  dsimp only
  have f := checks_fields T good letter tp sp A mem t read
  unfold HistoryBatchTape.Header.row
  rw [f.1,f.2.1]
  exact BatchRows.record_at _ _ _ _ (checks_dimensions T good letter tp sp A mem t read z) _ i

include read in
theorem payload_row (i : Fin (r+e)) :
    let X := pieces (checkedTile T.rule T.table) PC
    copy ⟨A.streams,A.maps,0,0⟩ (fun j => (X j).wire) (fun j => Tree.atom (X j).N) i = (PA).row i.val := by
  dsimp only
  have f := payload_fields T good letter tp sp A mem t read
  unfold HistoryBatchTape.Header.row
  rw [f.1,f.2.1]
  exact BatchRows.record_at _ _ _ _ (payload_dimensions T good letter tp sp A mem t read) _ i

end Party
end

end ThreeFlat.RAM.HistoryPartySpecialization

end OAI
