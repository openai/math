import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyIndex
import OAI.Computability.NearSquareRoot.InterchangeTemplateData
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasCodec
import OAI.Computability.NearSquareRoot.InterchangeVerifiedAtlas

/-! # Canonical native rectangle geometry of a verified raw template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data
open InterchangeROMStage FlatAtlas RectangleAtlas InterchangeROMRepair

variable {j threshold : ℕ} {x : Data}

/-- The geometric fields used by the literal stage generator. -/
def roleFrame (x : Data) : InterchangeROMStage.Frame :=
  (x.m,x.labels,x.rectangles,x.mask,x.row,x.col)

def rect (x : Data) (b : Fin x.rectangles) : Rectangle (Fin x.labels) where
  sources := Finset.univ.filter fun v => FlatAtlas.mask x.mask x.labels x.rectangles false b v
  destinations := Finset.univ.filter fun v => FlatAtlas.mask x.mask x.labels x.rectangles true b v

theorem rect_represents (x : Data) : Represents x.mask x.rect := by
  intro s b v
  cases s <;> simp [rect]

theorem rect_mask (x : Data) : TemplateMasks.MaskRepresents x.mask x.rect :=
  fun s b v => (x.rect_represents s b v).symm

theorem incident_degree (h : Valid j threshold x) (s : Bool) (v : Fin x.labels) :
    Fintype.card (StageLedger.Incident x.rect s v) ≤ x.inc := by
  rw [← TemplateMasks.degree_eq _ _ x.rect_mask]
  cases s
  · exact h.2.1.1 v v.isLt
  · exact h.2.1.2 v v.isLt

def rowSel (h : Valid j threshold x) : Fin x.rank → Fin x.labels :=
  NumericMinor.selected x.row h.2.2.1.1

def colSel (h : Valid j threshold x) : Fin x.rank → Fin x.labels :=
  NumericMinor.selected x.col h.2.2.1.2.1

theorem minor_lengths (h : Valid j threshold x) : x.row.length = x.rank ∧ x.col.length = x.rank := by
  obtain ⟨_,_,_,_,_,_,_,hr,hc⟩ := h.1
  exact ⟨hr,hc⟩

/-- This realization reads the mask and both selections directly from the accepted data. -/
def roleRealization (h : Valid j threshold x) : Frame.Realization x.roleFrame where
  rank := x.rank
  rect := x.rect
  sel s := if s then rowSel h else colSel h
  minor_length s := by cases s <;> first | exact (minor_lengths h).1 | exact (minor_lengths h).2
  minor_get s i := by
    have ℓ := minor_lengths h
    cases s
    · change x.col[i.val]? = some (NumericMinor.index x.col i.val)
      have lt : i.val < x.col.length := ℓ.2.symm ▸ i.isLt
      rw [NumericMinor.index,List.getD_eq_getElem _ _ lt,List.getElem?_eq_getElem lt]
    · change x.row[i.val]? = some (NumericMinor.index x.row i.val)
      have lt : i.val < x.row.length := ℓ.1.symm ▸ i.isLt
      rw [NumericMinor.index,List.getD_eq_getElem _ _ lt,List.getElem?_eq_getElem lt]
  incident_iff s v b := by
    change x.mask[(s.toNat*x.rectangles+b.val)*x.labels+v.val]?.getD false = true ↔
      v ∈ if s then (x.rect b).destinations else (x.rect b).sources
    rw [← List.getD_eq_getElem?_getD]
    exact x.rect_represents s b v

theorem good_modulus (h : Valid j threshold x) : x.modulusIndex+1 = x.p := by
  have hp := h.1.1.pos
  change x.p - 1 + 1 = x.p
  omega

theorem good_prime (h : Valid j threshold x) : Nat.Prime (x.modulusIndex+1) := good_modulus h ▸ h.1.1

def middleMatrix (x : Data) : Matrix (Fin x.rank) (Fin x.rank) (ZMod (x.modulusIndex+1)) :=
  Raw.interpret x.modulusIndex x.rank x.rank (Raw.read x.rank x.middle)

theorem minor_valid (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    MinorROM.valid (rectangleMatrix (K:=ZMod (x.modulusIndex+1)) x.rect)
      ⟨rowSel h,colSel h,x.middleMatrix⟩ = true := by
  have eq := (NumericMinor.laws_iff x.labelMatrix (Raw.read x.rank x.middle) x.row x.col
    h.2.2.1.1 h.2.2.1.2.1).mp h.2.2.1
  rw [show Raw.interpret x.modulusIndex x.labels x.labels x.labelMatrix =
    rectangleMatrix x.rect from TemplateMasks.matrix_eq _ _ _ _ _ x.rect_mask] at eq
  exact eq

/-- The inverse minor and the row/column selections stored in the template give
the exact factorization required by the shared rectangle sweep. -/
theorem minor_factor (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    let A := rectangleMatrix (K:=ZMod (x.modulusIndex+1)) x.rect
    A.submatrix id (colSel h) * x.middleMatrix * A.submatrix (rowSel h) id = A :=
  ((MinorROM.valid_iff _ _).mp (minor_valid h)).2.2.2

theorem radix_gt_one (h : Valid j threshold x) : 1 < x.b := h.1.2.2.1.one_lt

/-- Decode every active native chart directly from its verified literal word. -/
def catalog (h : Valid j threshold x) : AddressROM.Catalog x.rect x.a x.m x.b :=
  fun c => Opcode.decodeWord (FlatAtlas.chart x.chart (chartIndex c)) (by
    have hc := ((valid_iff_on x.rect_represents x.chart).mp h.2.2.2.1).1 c
    simp only [FlatAtlas.shape,Bool.and_eq_true] at hc
    exact hc.1)

theorem catalog_word (h : Valid j threshold x) (c : Chart x.rect x.m) :
    FlatAtlas.chart x.chart (chartIndex c) = ((catalog h) c).map Opcode.encode :=
  (Opcode.encode_decodeWord _ _).symm

theorem catalog_valid (h : Valid j threshold x) : AddressROM.valid (catalog h) = true :=
  (catalog_iff x.rect_represents (radix_gt_one h) _ _ (catalog_word h)).mp h.2.2.2.1

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
