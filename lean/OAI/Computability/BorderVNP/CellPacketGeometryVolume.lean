import OAI.Computability.BorderVNP.CellPacketGeometryRate
import OAI.Computability.BorderVNP.CellPacketGeometryBoundaries

/-! # Charging the true padded public geometry by its declared sparse row formats -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open CellSparse CellSparse.Packet Packing.BankPacket SiteWords
open private headers_length counts_length from OAI.Computability.BorderVNP.CellPacketGeometrySpanShape

variable {s C : ℕ} {E I Orig : Type} [Fintype E]

omit [Fintype E] in
/-- The chronological word count is the sum of the fixed body lengths after
removing each source site's own record count. -/
theorem Template.recordSlots_sum (T : Template E I Orig s C) :
    T.recordSlots.length = ∑ i, ((tape (T.format i)).length-1) := by
  simp [Template.recordSlots,List.length_flatMap,←List.ofFn_eq_map,List.sum_ofFn]

/-- Site-tape and raw scalar source columns occur once in the source frame. -/
theorem Template.fields_count (T : Template E I Orig s C) :
    Fintype.card T.Fields = Fintype.card E+s+T.recordSlots.length := by
  have each (i : Fin s) : (tape (T.format i)).length = 1+((tape (T.format i)).length-1) := by simp [tape,Nat.add_comm]
  have summed := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => each i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    mul_one,←Template.recordSlots_sum] at summed
  simp only [Template.Fields,Template.RowPin,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,summed]
  omega

omit [Fintype E] in
/-- Raw source stream arity counts public boxes, fixed record fields and actual
report address vectors. Opaque factor payloads contribute no words. -/
theorem Template.atoms_count (T : Template E I Orig s C) (baseOwner : Fin s → Fin C) :
    T.atoms.length = 3*C+(∑ i, (boxWords (T.boxes i)).length)+T.recordSlots.length+
      ∑ c, T.reportWordCount c := by
  let args : E → ℕ := fun _ => 0
  let fields : Fin s → I → ℕ := fun _ _ => 0
  let D := T.directory baseOwner args fields
  have raw := D.recordPieces_words id
  have records : D.recordRows.length = T.recordSlots.length := by
    rw [← raw,List.length_map]
    exact T.recordSlots_length id args fields
  have boxes : D.boxRows.length = ∑ i, (boxWords (T.boxes i)).length := by
    simp only [Directory.boxRows,siteRows_length,D,Template.directory,←List.ofFn_eq_map,List.sum_ofFn]
  have reports : D.reportRows.length = ∑ c, T.reportWordCount c := by
    simp only [Directory.reportRows,cellRows,siteRows_length,←List.ofFn_eq_map,List.sum_ofFn]
    exact Finset.sum_congr rfl fun c _ => (T.reportWordCount_eq baseOwner args fields c).symm
  have eqn : D.words.length = T.atoms.length := T.wordCapacity baseOwner args fields
  simp only [Directory.words,List.length_append,headers_length,counts_length,boxes,records,reports] at eqn
  omega

/-- Expanded public volume in the exact true input shapes. The formula can be
applied before site assignments are known, including inactive sparse row slots. -/
theorem Template.publicVolume_fields (T : Template E I Orig s C) (baseOwner : Fin s → Fin C) :
    T.publicVolume = 1+2*s+9*C+3*T.recordSlots.length+Fintype.card E+
      (∑ i, (T.boxes i).length)+(∑ i, (boxWords (T.boxes i)).length)+(∑ c, T.reportWordCount c)+
      ∑ z : T.RowPin, (tape (T.format z.1))[z.2].nodes := by
  rw [Template.publicVolume,T.atoms_count baseOwner,T.chunkLabels_length,T.fields_count]
  simp only [List.length_flatMap,←List.ofFn_eq_map,List.sum_ofFn]
  omega

/-- A bounded number of expression nodes per scalar gives a pure sparse
shape estimate suitable for the physical time envelope. -/
theorem Template.publicVolume_le (T : Template E I Orig s C) (baseOwner : Fin s → Fin C) (nodes : ℕ)
    (fields : ∀ z : T.RowPin, (tape (T.format z.1))[z.2].nodes ≤ nodes) :
    T.publicVolume ≤ 1+2*s+9*C+3*T.recordSlots.length+Fintype.card E+
      (∑ i, (T.boxes i).length)+(∑ i, (boxWords (T.boxes i)).length)+(∑ c, T.reportWordCount c)+
      (s+T.recordSlots.length)*nodes := by
  rw [T.publicVolume_fields baseOwner]
  apply Nat.add_le_add_left
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => fields i)
  have card : Fintype.card T.RowPin = s+T.recordSlots.length := by
    have eqn := T.fields_count
    simp only [Template.Fields,Fintype.card_sum] at eqn
    omega
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,card] using h

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
