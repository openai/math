import OAI.Computability.BorderVNP.CellPacketGeometryNative
import OAI.Computability.BorderVNP.CellPacketGeometryReferences

/-! # Physical source arrays before the supplemental record prepass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open CellSparse CellSparse.Packet
open CellSparse.Packet.Source (boxPart plan chunks)
open RoutingISA.CellPacket

variable {C p d H dest : ℕ} {S Orig E : Type} {D : SiteWords.Directory S Orig C}
variable {pin : Orig → E} {arg : E → ℕ} {slot : Orig → ℕ} {mem : ℕ → ℕ}
variable {fit : C+D.words.length+C ≤ 2^p} {space : C+(coords (D.referenceRows pin).length).length+C ≤ 2^d}
variable {π : Equiv.Perm (Fin (2^p))}

private theorem selected_eq (D : SiteWords.Directory S Orig C) (pin : Orig → E) (c : Fin C) :
    ((List.finRange (D.referenceRows pin).length).filter
      (fun i => decide (((D.referenceRows pin).get i).1 = c))).map (fun i => ((D.referenceRows pin).get i).2) =
    D.cellReferences pin c ++ [.blank,.blank,.blank] := by
  have eqn := congrArg (fun ys : List (Fin C × Reference D.words.length E) =>
    (ys.filter (fun r => decide (r.1=c))).map Prod.snd) (List.map_get_finRange (D.referenceRows pin))
  refine Eq.trans ?_ (D.filter_referenceRows pin c)
  simpa only [List.filter_map,List.map_map,Function.comp_def] using eqn

private theorem links_length {N : ℕ} {owner : Fin N → Fin C} {c : Fin C} {pos : ℕ}
    {ps : List (Source.Part Orig)} {rs : List (Reference N E)} (h : Links owner c arg slot pos ps rs) :
    rs.length = ps.length := by
  induction h with
  | nil => rfl
  | words _ _ _ _ _ _ _ _ ih | site _ _ _ _ ih => simp only [List.length_cons,ih]

/-- The physical descriptor interval contains the native chunks of this cell and
three all-zero reservations at the addresses read from its two marker banks. -/
theorem Buffers.reserved
    (h : Buffers D fit space dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) arg mem π)
    (addr : ∀ a, arg (pin a) = slot a) (fs : Orig → List Factor) (c : Fin C) :
    let pub := sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)
    let tab := sectionRange mem (descriptorBank dest p) (Markers.start space c) (Markers.stop space c)
    let parts := plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)
    tab.2 = 3*(parts.length+3) ∧
      WordsAt mem tab.1 (descriptors (Source.chunks slot H fs pub.1 parts) ++ List.replicate 9 0) := by
  intro pub tab parts
  obtain ⟨length,stored⟩ := h.chunks c
  rw [selected_eq] at length stored
  have link := D.links_cellReferences pin arg slot addr c
  have base : pub.1 = dest+(π.symm (Markers.start fit c)).val+1 := by simp [pub,sectionRange,h.positions]
  refine ⟨by simpa only [List.length_append,links_length link,List.length_cons,List.length_nil] using length,?_⟩
  have desc := link.descriptors fit dest H fs π h.sorted
  simp only [Nat.add_zero,← base] at desc
  have blanks : ([0,0,0] ++ ([0,0,0] ++ ([0,0,0] ++ [])) : List ℕ) = List.replicate 9 0 := by decide
  simpa only [List.flatMap_append,desc,List.flatMap_cons,Reference.values_blank,List.flatMap_nil,blanks] using stored

/-- Initial header and box parts, before the combined record and report section. -/
def prefixParts (D : SiteWords.Directory S Orig C) (c : Fin C) : List (Source.Part Orig) :=
  .publicWords [D.privateWires c,(D.cellBoxes c).length] :: (D.cellBoxes c).map boxPart

private theorem chunks_append (fs : Orig → List Factor) (pre post : List (Source.Part Orig)) (base : ℕ) :
    chunks slot H fs base (pre++post) = chunks slot H fs base pre ++
      chunks slot H fs (base+(pre.flatMap Source.Part.publicBuffer).length) post := by
  induction pre generalizing base with
  | nil => simp [chunks]
  | cons x pre ih =>
    cases x <;> simp [chunks,Source.Part.publicBuffer,ih,Nat.add_assoc]

/-- The last ordinary descriptor, the three unused triples, and the record and
report data are all at the addresses used by the subsequent native prepass. -/
theorem Buffers.reserved_split
    (h : Buffers D fit space dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) arg mem π)
    (addr : ∀ a, arg (pin a) = slot a) (fs : Orig → List Factor) (c : Fin C) :
    let pub := sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)
    let tab := sectionRange mem (descriptorBank dest p) (Markers.start space c) (Markers.stop space c)
    let pre := prefixParts D c
    let tailBase := pub.1+(pre.flatMap Source.Part.publicBuffer).length
    let rows := (D.cellRecords c).flatMap record
    let reports := fieldList vector (D.reports c)
    WordsAt mem tab.1 (descriptors (Source.chunks slot H fs pub.1 pre) ++
      [0,tailBase,1+rows.length+reports.length] ++ List.replicate 9 0) ∧
      mem tailBase = (D.cellRecords c).length ∧ WordsAt mem (tailBase+1) rows ∧
      WordsAt mem (tailBase+1+rows.length) reports := by
  intro pub tab pre tailBase rows reports
  have plan_eq : plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c) =
      pre ++ [.publicWords (fieldList record (D.cellRecords c) ++ reports)] := rfl
  have stored := (h.reserved addr fs c).2
  rw [plan_eq,chunks_append] at stored
  have data := (h.publicWords c).2
  rw [plan_eq] at data
  simp only [List.flatMap_append,List.flatMap_singleton,Source.Part.publicBuffer] at data
  have head := data.right
  have bytes : WordsAt mem tailBase ([(D.cellRecords c).length] ++ (rows++reports)) := head
  refine ⟨?_,?_,bytes.right.left,bytes.right.right⟩
  · simpa only [tailBase,rows,descriptors,List.flatMap_append,Source.chunks,List.flatMap_singleton,Chunk.descriptor,
      fieldList,List.length_append,List.length_cons,Nat.add_comm 1] using stored
  · simpa only [Nat.add_zero,List.getElem_cons_zero] using bytes.left ⟨0,by simp⟩

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI
