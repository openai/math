import OAI.Computability.BorderVNP.CellPacketChunk
import OAI.Computability.BorderVNP.CellSerializedLength
import OAI.Computability.BorderVNP.TransmissionSiteStrings

/-! # Public words and private one-copy site strings in a cell packet

The public shape lists local boxes by ordinal. The initial wiring, relative bit numbers
and row tables of an original site are encoded only in its delivered string. A private
length header delimits the payload within the common public reservation. Repetitions
refer to the ordinal through `Record.box` and do not duplicate the string.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Source

open BorderVNP.RoutingISA.CellPacket
open BorderVNP.RoutingISA.CellPacketEncode (packet)
open BorderVNP.CellMacro.Generator (records records_append)

private theorem frame_append (xs ys : List ℕ) : packet (xs ++ ys) = packet xs ++ packet ys := by
  simp only [packet, List.map_append, records_append]

/-- All relative wire numbers and tables in one original site, including the factor count. -/
def boxBody (fs : List Factor) : List Bool := packet (fieldList factor fs)

/-- A private site string begins with its true payload length in a fixed-width word.
Its tail is zero-filled to the public description width when read by `siteString`. -/
def siteData (width : ℕ) (fs : List Factor) : List Bool :=
  List.ofFn (fun i : Fin width => (boxBody fs).length.testBit i.val) ++ boxBody fs

/-- Original private string at the width reserved by the delivery directory. -/
def siteString {description : ℕ} (width : ℕ) (fs : List Factor) (b : Fin description) : Bool :=
  ((siteData width fs)[b.val]?).getD false

/-- Meaningful box bytes in the delivered reservation. A separate tally list may use
the rest of that reservation. -/
def Delivered {description : ℕ} (mem : ℕ → ℕ) (slot width : ℕ) (fs : List Factor) : Prop :=
  ∀ b : Fin description, b.val < (siteData width fs).length → mem (slot + b.val) = (siteString width fs b).toNat

/-- The native opaque chunk reads its header and unpadded body from the delivered site.
No public descriptor exposes the used length. -/
theorem box_stored {description : ℕ} (mem : ℕ → ℕ) (slot width : ℕ) (fs : List Factor)
    (sent : Delivered (description := description) mem slot width fs)
    (room : width + (boxBody fs).length ≤ description) (fits : (boxBody fs).length < 2^width) :
    (Chunk.box slot width (boxBody fs)).Stored mem := by
  refine ⟨fits, fun i => ?_, fun i => ?_⟩
  · have h := sent ⟨i.val,by have := i.isLt; omega⟩ (by simp [siteData]; have := i.isLt; omega)
    simpa [siteString,siteData,List.getElem?_append_left, i.isLt] using h
  · have h := sent ⟨width+i.val,by have := i.isLt; omega⟩ (by simp [siteData])
    simpa [siteString,siteData,List.getElem?_append_right, i.isLt,Nat.add_assoc] using h

/-- Public blocks include shape words, profile records and any fixed crossing boxes.
An original bottom box is named only by its private-delivery key. -/
inductive Part (Site : Type) where
  | publicWords (xs : List ℕ)
  | original (site : Site)

/-- Words specified by geometry, excluding the contents of original site boxes. -/
def Part.publicBuffer {Site : Type} : Part Site → List ℕ
  | .publicWords xs => xs
  | .original _ => []

/-- The expected encoded stream of a single part. -/
def Part.denote {Site : Type} (fs : Site → List Factor) : Part Site → List Bool
  | .publicWords xs => packet xs
  | .original j => boxBody (fs j)

/-- Native chunks in final stream order. Only public groups consume addresses from the
public word buffer. Every original box descriptor uses the common header width. -/
def chunks {Site : Type} (slot : Site → ℕ) (width : ℕ) (fs : Site → List Factor) :
    ℕ → List (Part Site) → List Chunk
  | _, [] => []
  | a, .publicWords xs :: ps => .words a xs :: chunks slot width fs (a + xs.length) ps
  | a, .original j :: ps => .box (slot j) width (boxBody (fs j)) :: chunks slot width fs a ps

/-- Changing arbitrary private wiring or table data does not alter any word of the
public descriptor array. -/
theorem descriptors_private {Site : Type} (slot : Site → ℕ) (width : ℕ)
    (fs gs : Site → List Factor) (parts : List (Part Site)) (base : ℕ) :
    descriptors (chunks slot width fs base parts) = descriptors (chunks slot width gs base parts) := by
  induction parts generalizing base with
  | nil => rfl
  | cons p ps ih => cases p <;> simp only [chunks, descriptors,List.flatMap_cons,Chunk.descriptor] at ih ⊢ <;> rw [ih]

/-- Each source meets the actual native reader's memory precondition. The required
inputs are a packed public word buffer and per-site delivery at its original slot. -/
theorem chunks_stored {Site : Type} {description : ℕ} (mem : ℕ → ℕ) (slot : Site → ℕ) (width : ℕ)
    (fs : Site → List Factor) (parts : List (Part Site)) (base : ℕ)
    (sent : ∀ j, Part.original j ∈ parts → Delivered (description := description) mem (slot j) width (fs j))
    (room : ∀ j, width + (boxBody (fs j)).length ≤ description)
    (fits : ∀ j, (boxBody (fs j)).length < 2^width)
    (pub : WordsAt mem base (parts.flatMap Part.publicBuffer)) :
    ∀ c ∈ chunks slot width fs base parts, c.Stored mem := by
  induction parts generalizing base with
  | nil => simp [chunks]
  | cons p ps ih =>
    intro c hc
    cases p with
    | publicWords xs =>
      change WordsAt mem base (xs ++ ps.flatMap Part.publicBuffer) at pub
      rcases List.mem_cons.mp hc with rfl | h
      · exact pub.left
      · exact ih _ (fun j hj => sent j (List.mem_cons_of_mem _ hj)) pub.right _ h
    | original j =>
      rcases List.mem_cons.mp hc with rfl | h
      · exact box_stored mem _ _ _ (sent j List.mem_cons_self) (room j) (fits j)
      · exact ih _ (fun k hk => sent k (List.mem_cons_of_mem _ hk)) pub _ h

private theorem chunks_bits {Site : Type} (slot : Site → ℕ) (width : ℕ)
    (fs : Site → List Factor) (parts : List (Part Site)) (base : ℕ) :
    (chunks slot width fs base parts).flatMap Chunk.bits = parts.flatMap (Part.denote fs) := by
  induction parts generalizing base with
  | nil => rfl
  | cons p ps ih => cases p <;> simp only [chunks,List.flatMap_cons,Chunk.bits,Part.denote,ih]

/-- A box ordinal denotes either a fixed public crossing box or an original site box. -/
abbrev Box (Site : Type) := List Factor ⊕ Site

/-- Resolve a box ordinal to its one-copy factors. -/
def factors {Site : Type} (fs : Site → List Factor) : Box Site → List Factor := Sum.elim id fs

/-- Public words for a fixed box, or one opaque slice for an original site. -/
def boxPart {Site : Type} : Box Site → Part Site
  | .inl fs => .publicWords (fieldList factor fs)
  | .inr j => .original j

/-- The cell's canonical ordered chunk schedule. Box IDs in `rows` refer to indices
in `boxes`, independently of the processor or source-slot numbering. -/
def plan {Site : Type} (privateWires : ℕ) (boxes : List (Box Site)) (rows : List Record)
    (reports : List (List ℕ)) : List (Part Site) :=
  .publicWords [privateWires,boxes.length] :: boxes.map boxPart ++
    [.publicWords (fieldList record rows ++ fieldList vector reports)]

private theorem box_parts {Site : Type} (fs : Site → List Factor) (boxes : List (Box Site)) :
    (boxes.map boxPart).flatMap (Part.denote fs) =
      packet ((boxes.map (factors fs)).flatMap (fieldList factor)) := by
  induction boxes with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [boxPart,factors,Part.denote,boxBody,frame_append,ih]

/-- The physical assembly yields exactly the bit input of `CellSparse.Packet`, including
private local relative indices, public repeat counts, and multiplicity-bit addresses. -/
theorem packet_bits {Site : Type} (slot : Site → ℕ) (width : ℕ)
    (fs : Site → List Factor) (privateWires : ℕ) (boxes : List (Box Site)) (rows : List Record)
    (reports : List (List ℕ)) (base : ℕ) :
    (chunks slot width fs base (plan privateWires boxes rows reports)).flatMap Chunk.bits =
      bits ⟨boxes.map (factors fs),rows,reports⟩ privateWires := by
  rw [chunks_bits]
  simp only [plan, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil,
    Part.denote, box_parts, bits, words, List.cons_append, List.nil_append, List.length_map, fieldList]
  change packet [_,_] ++ (_ ++ _) = packet _
  simp only [← frame_append, List.cons_append, List.nil_append, List.append_assoc]

/-- Original private IDs in the schedule, in order. -/
def privateKeys {Site : Type} (parts : List (Part Site)) : List Site :=
  parts.filterMap fun | .original j => some j | .publicWords _ => none

/-- Each original site entry appears once per box ordinal regardless of how many rows
and copies refer to that ordinal. -/
theorem privateKeys_plan {Site : Type} (privateWires : ℕ) (boxes : List (Box Site))
    (rows : List Record) (reports : List (List ℕ)) :
    privateKeys (plan privateWires boxes rows reports) = boxes.filterMap Sum.getRight? := by
  simp only [privateKeys, plan, List.filterMap_cons, List.filterMap_append, List.filterMap_map,
    List.filterMap_nil, List.append_nil]
  congr 1
  funext b; cases b <;> rfl

/-- Public slot order assigns every original site of the cell one box ordinal. -/
def cellSites (entries : ℕ) (placed : ℕ → ℕ × ℕ) (cell : ℕ) : List (Fin entries) :=
  (List.finRange entries).filter fun j => decide ((placed j.val).1 = cell)

/-- The bottom bundles' site directory never requests a private site twice. -/
theorem privateKeys_once (entries : ℕ) (placed : ℕ → ℕ × ℕ) (cell privateWires : ℕ)
    (paid : List (List Factor)) (rows : List Record) (reports : List (List ℕ)) :
    (privateKeys (plan privateWires (paid.map Sum.inl ++ (cellSites entries placed cell).map Sum.inr)
      rows reports)).Nodup := by
  rw [privateKeys_plan]
  simp [List.filterMap_map, Function.comp_def, Sum.getRight?,cellSites]
  exact (List.nodup_finRange entries).filter _

/-- Sparse reader work charged to each public word block and once per original site.
The box term uses the padded description cap, independent of all repeat counts. -/
theorem chunks_work_le {Site : Type} (slot : Site → ℕ) (width description w : ℕ)
    (fs : Site → List Factor) (parts : List (Part Site)) (base : ℕ)
    (room : ∀ j, width + (boxBody (fs j)).length ≤ description) :
    ((chunks slot width fs base parts).map (Chunk.work w)).sum ≤
      (parts.map (fun | .publicWords xs => 60*(xs.length+1)*(w+1)
                      | .original _ => 60*(description+1))).sum := by
  induction parts generalizing base with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | publicWords xs => exact Nat.add_le_add_left (ih _) _
    | original j => exact Nat.add_le_add (Nat.mul_le_mul_left 60 (Nat.succ_le_succ (room j))) (ih _)

/-- A public cap on the original bodies gives a single common header and padded
description width, chosen independently of the private wiring. -/
theorem siteData_room (fs : List Factor) (cap : ℕ) (bounded : (boxBody fs).length ≤ cap) :
    (siteData cap.size fs).length ≤ cap.size + cap ∧ (boxBody fs).length < 2^cap.size := by
  exact ⟨by simpa [siteData] using bounded,bounded.trans_lt (Nat.lt_size_self cap)⟩

end CellSparse.Packet.Source

end BorderVNP
end Computability
end OAI
