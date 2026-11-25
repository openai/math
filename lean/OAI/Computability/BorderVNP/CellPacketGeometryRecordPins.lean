import OAI.Computability.BorderVNP.CellPacketGeometryRegroupRefs
import OAI.Computability.BorderVNP.CellPacketGeometryLiveRun

/-! # Fixed positions of the scalar row block and its true site-owner source pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open CellSparse CellSparse.Packet Packing.BankPacket SiteWords
open private headers_length counts_length from OAI.Computability.BorderVNP.CellPacketGeometrySpanShape
open private row_length from OAI.Computability.BorderVNP.CellPacketGeometryFixedReferences

variable {s C : ℕ} {E I Orig : Type}

/-- Start of the sole word block requiring a site-major stable sort. -/
def Template.recordStart (T : Template E I Orig s C) :=
  C*2+((List.finRange s).map fun i => (boxWords (T.boxes i)).length).sum+C

/-- One chronological piece-slot reference for each emitted scalar record word,
excluding the redundant count word of each piece. -/
def Template.recordSlots (T : Template E I Orig s C) : List (Fin s) :=
  (List.finRange s).flatMap fun i => List.replicate ((tape (T.format i)).length-1) i

/-- Numerical input and dynamic site labels never alter the block's first position. -/
theorem Template.recordStart_eq (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (args : E → ℕ) (fields : Fin s → I → ℕ) :
    let D := T.directory owner args fields
    (D.headers++D.boxRows++D.counts).length = T.recordStart := by
  intro D
  simp only [List.length_append,headers_length,counts_length,Directory.boxRows,siteRows_length]
  rfl

/-- Reading the actual site owner of each fixed input reference recovers all
keys in the chronological physical scalar stream. -/
theorem Template.recordSlots_keys (T : Template E I Orig s C) (anchor : Fin s → Fin s)
    {cells : Fin s → Fin C} (args : E → ℕ) (fields : Fin s → I → ℕ) :
    T.recordSlots.map anchor = ((T.directory cells args fields).recordPieces anchor).map Prod.fst := by
  simp only [Template.recordSlots,Directory.recordPieces,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro i _
  simp only [tag,Template.directory,List.map_replicate,List.map_map,Function.comp_def,List.map_const',row_length]

/-- Total input field count of the site sort, including the fields of every
live origin, terminal, retained layer and physical padding row. -/
theorem Template.recordSlots_length (T : Template E I Orig s C) (anchor : Fin s → Fin s)
    {owner : Fin s → Fin C} (args : E → ℕ) (fields : Fin s → I → ℕ) :
    ((T.directory owner args fields).recordPieces anchor).length = T.recordSlots.length := by
  simpa only [List.length_map] using (congrArg List.length (T.recordSlots_keys (cells := owner) anchor args fields)).symm

/-- The hardwired word block fits inside the global sparse public source bank. -/
theorem Template.recordRoom (T : Template E I Orig s C) (baseOwner : Fin s → Fin C) :
    T.recordStart+T.recordSlots.length ≤ T.atoms.length := by
  let D := T.directory baseOwner (fun _ => 0) (fun _ _ => 0)
  have hp : (D.headers++D.boxRows++D.counts).length = T.recordStart := T.recordStart_eq ..
  have hs : (D.recordPieces id).length = T.recordSlots.length := T.recordSlots_length id _ _
  have hr := congrArg List.length (D.recordPieces_words id)
  simp only [List.length_map] at hr
  have hw : D.words.length = T.atoms.length := T.wordCapacity ..
  simp only [Directory.words,List.length_append] at hp hw
  omega

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
