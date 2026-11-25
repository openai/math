import OAI.Computability.NearSquareRoot.InterchangeTemplateMasks
import OAI.Computability.NearSquareRoot.InterchangeTemplateCost
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasCheck
import OAI.Computability.NearSquareRoot.InterchangeROMRepairCompiler
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCharacteristic

/-!
# Finite ROM for a recursive interchange node

The header stores the ground characteristic, native radix, number of main
coordinates, reserve dimension, label and rectangle counts, rank, and maximum
incidence. The remaining tables hold both incidence masks, all native chart
words, the two minor selections, its inverse, and the ground-field repair.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template

open InterchangeROMRepair

abbrev Data := (List ℕ × List Bool) ×
  (List Opcode.Word × List ℕ × List ℕ × List ℕ × Raw.Tape)

namespace Data

def header (x : Data) (i : ℕ) := x.1.1.getD i 0
abbrev p (x : Data) := x.header 0
abbrev b (x : Data) := x.header 1
abbrev m (x : Data) := x.header 2
abbrev a (x : Data) := x.header 3
abbrev labels (x : Data) := x.header 4
abbrev rectangles (x : Data) := x.header 5
abbrev rank (x : Data) := x.header 6
abbrev inc (x : Data) := x.header 7
abbrev mask (x : Data) := x.1.2
abbrev chart (x : Data) := x.2.1
abbrev row (x : Data) := x.2.2.1
abbrev col (x : Data) := x.2.2.2.1
abbrev middle (x : Data) := x.2.2.2.2.1
abbrev repair (x : Data) := x.2.2.2.2.2
abbrev modulusIndex (x : Data) := x.p-1
abbrev labelMatrix (x : Data) := TemplateMasks.matrix x.mask x.labels x.rectangles
abbrev width (x : Data) := TemplateCost.width x.m x.labels
abbrev calls (x : Data) := TemplateCost.calls x.m x.a x.labels x.rank x.inc

def sizeChecks (threshold : ℕ) (x : Data) : Prop :=
  x.p.Prime ∧ 2 < x.p ∧ x.b.Prime ∧ threshold < x.b ∧ x.width < x.b ∧
    2 ≤ x.m ∧ 0 < x.labels ∧ x.row.length = x.rank ∧ x.col.length = x.rank

def degreeChecks (x : Data) : Prop :=
  (∀ v < x.labels, TemplateMasks.degree x.mask x.labels x.rectangles false v ≤ x.inc) ∧
  (∀ v < x.labels, TemplateMasks.degree x.mask x.labels x.rectangles true v ≤ x.inc)

def Valid (j threshold : ℕ) (x : Data) : Prop :=
  x.sizeChecks threshold ∧ x.degreeChecks ∧
  NumericMinor.laws x.modulusIndex x.labels x.rank x.labelMatrix (Raw.read x.rank x.middle) x.row x.col ∧
  FlatAtlas.valid x.b x.a x.m x.labels x.rectangles x.mask x.chart = true ∧
  Raw.Valid x.modulusIndex (Raw.rowCount x.m) (Raw.checkCount x.m) x.m (Sizes.pencilOrder x.m)
    (Raw.halfCode x.modulusIndex) x.repair ∧
  TemplateCost.accept j x.m x.a x.b x.width x.calls = true

instance (threshold : ℕ) (x : Data) : Decidable (sizeChecks threshold x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

instance (x : Data) : Decidable (degreeChecks x) :=
  inferInstanceAs (Decidable ((∀ v < x.labels, TemplateMasks.degree x.mask x.labels x.rectangles false v ≤ x.inc) ∧
    (∀ v < x.labels, TemplateMasks.degree x.mask x.labels x.rectangles true v ≤ x.inc)))

instance (j threshold : ℕ) (x : Data) : Decidable (Valid j threshold x) :=
  inferInstanceAs (Decidable (x.sizeChecks threshold ∧ x.degreeChecks ∧
    NumericMinor.laws _ _ _ _ _ _ _ ∧ _ = true ∧ Raw.Valid _ _ _ _ _ _ _ ∧ _ = true))

theorem primrec_header (i : ℕ) : Primrec fun x : Data => x.header i :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp .fst) (.const i)

theorem primrec_mask : Primrec mask := Primrec.snd.comp .fst
theorem primrec_chart : Primrec chart := Primrec.fst.comp .snd
theorem primrec_row : Primrec row := Primrec.fst.comp (Primrec.snd.comp .snd)
theorem primrec_col : Primrec col := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd))
theorem primrec_middle : Primrec middle := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
theorem primrec_repair : Primrec repair := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
theorem primrec_modulusIndex : Primrec modulusIndex := Primrec.nat_sub.comp (primrec_header 0) (.const 1)
theorem primrec_width : Primrec width := TemplateCost.primrec_width (primrec_header 2) (primrec_header 4)
theorem primrec_calls : Primrec calls := TemplateCost.primrec_calls (primrec_header 2) (primrec_header 3)
  (primrec_header 4) (primrec_header 6) (primrec_header 7)

theorem primrec_sizeChecks : PrimrecRel sizeChecks := by
  let h (i) := (primrec_header i).comp (Primrec.snd (α:=ℕ) (β:=Data))
  exact ((Generator.primrecPrime.comp (h 0)).and ((Primrec.nat_lt.comp (.const 2) (h 0)).and
    ((Generator.primrecPrime.comp (h 1)).and ((Primrec.nat_lt.comp .fst (h 1)).and
    ((Primrec.nat_lt.comp (primrec_width.comp .snd) (h 1)).and ((Primrec.nat_le.comp (.const 2) (h 2)).and
    ((Primrec.nat_lt.comp (.const 0) (h 4)).and
    ((Primrec.eq.comp (Primrec.list_length.comp (primrec_row.comp .snd)) (h 6)).and
      (Primrec.eq.comp (Primrec.list_length.comp (primrec_col.comp .snd)) (h 6)))))))))).primrecRel

theorem primrec_degreeChecks : PrimrecPred degreeChecks := by
  have side (s : Bool) : PrimrecPred fun x : Data => ∀ v < x.labels,
      TemplateMasks.degree x.mask x.labels x.rectangles s v ≤ x.inc :=
    Raw.bounded (primrec_header 4) (Primrec.nat_le.comp
      (TemplateMasks.primrec_degree s (primrec_mask.comp .fst) ((primrec_header 4).comp .fst)
      ((primrec_header 5).comp .fst) .snd) ((primrec_header 7).comp .fst))
  exact (side false).and (side true)

theorem valid_contraction {j t : ℕ} {x : Data} (h : Valid j t x) :
    ((x.calls * BatchRows.groups x.b x.width : ℕ) : ℝ) / x.b + (2*x.a : ℕ) <
      (x.m : ℝ)^Generator.targetExponent j := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    (TemplateCost.accept_iff _ _ _ _ _ _ h.1.2.2.1.pos).mp h.2.2.2.2.2

end Data
end Interchange.Template

end NearSquareRoot
end Computability
end OAI
