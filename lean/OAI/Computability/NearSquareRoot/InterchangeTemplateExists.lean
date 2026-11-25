import OAI.Computability.NearSquareRoot.InterchangeTemplateData
import OAI.Computability.NearSquareRoot.InterchangeTemplateGeometry
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasTransfer
import OAI.Computability.NearSquareRoot.InterchangeMinorPacking

/-!
# Existence of a passing interchange ROM

Number the labels and rectangles of the contracted Hamming frame and encode
its two incidence masks, address catalog, and selected rank minor in that
numbering. The repair-table witness uses the same odd characteristic and
the same number of main coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open InterchangeROMRepair

theorem exists_valid (j threshold : ℕ) : ∃ x : Data, x.Valid j threshold := by
  classical
  obtain ⟨p,hp,odd,m,hm,k,stage⟩ := TemplateCost.exists_frame j threshold
  cases p with
  | zero => omega
  | succ p =>
    let := hp
    obtain ⟨_,atlas,b,prime,above,⟨frame⟩,_,contract⟩ := stage
    let L := HammingLabels (p+1) k
    let B := HammingRectangleKey (p+1) k hp.out.pos
    let n := Fintype.card L
    let t := Fintype.card B
    let e := Fintype.equivFin L
    let d := Fintype.equivFin B
    let r := nodeRectangles (p+1) k
    let ord := TemplateGeometry.rect e d r
    let bits := TemplateGeometry.maskBits ord
    let a := hammingReserve (p+1) k
    let h := (hammingLabelMatrix (p+1) (2^k)).rank
    let inc := labelIncidence (p+1) k hp.out.pos
    have repr : FlatAtlas.Represents bits ord := TemplateGeometry.represents_maskBits ord
    have native : TemplateMasks.MaskRepresents bits ord := fun s v w => (repr s v w).symm
    have deg (s : Bool) (u : Fin n) : TemplateMasks.degree bits n t s u ≤ inc :=
      (TemplateMasks.degree_eq bits ord native s u).trans_le (TemplateGeometry.card_hamming_incident e d s u)
    obtain ⟨ws,validW,_⟩ := AddressROM.complete prime.one_lt frame
    have vord := TemplateGeometry.valid_catalog e d r ws validW
    obtain ⟨charts,vcharts,_,_⟩ := FlatAtlas.exists_table_of_catalog repr prime.one_lt _ vord
    obtain ⟨c,hc⟩ := MinorROM.complete (hammingLabelMatrix (p+1) (2^k))
    have hmtrx : rectangleMatrix (K:=ZMod (p+1)) r = hammingLabelMatrix (p+1) (2^k) :=
      rectangleMatrix_hammingRectangle _ _
    have hnum : MinorROM.valid (Raw.interpret p n n (TemplateMasks.matrix bits n t))
        (TemplateGeometry.minor e c) = true := by
      rw [TemplateMasks.matrix_eq p n t bits ord native]
      exact TemplateGeometry.valid_rect_minor e d r c (hmtrx.symm ▸ hc)
    obtain ⟨rs,cs,mid,hr,hc',check⟩ := NumericMinor.exists_encoding _ _ hnum
    obtain ⟨tape,htape⟩ := Raw.exists_valid hp.out odd hm
    have pos : 0 < n := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨fun _ _ => ⟨0, by positivity⟩⟩
    let x : Data := (([p+1,b,m,a,n,t,h,inc],bits),charts,rs,cs,mid,tape)
    refine ⟨x,?_,?_,check,vcharts,htape,contract⟩
    · exact ⟨hp.out,odd,prime,(le_max_left _ _).trans_lt above,(le_max_right _ _).trans_lt above,hm,pos,hr,hc'⟩
    · exact ⟨fun v hv => deg false ⟨v,hv⟩,fun v hv => deg true ⟨v,hv⟩⟩

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
