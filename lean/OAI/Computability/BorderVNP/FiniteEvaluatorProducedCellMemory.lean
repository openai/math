import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands
import OAI.Computability.BorderVNP.CellPacketSourceSize

/-! # The finite task's descriptor marker span and private prepass memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Packing.Inherited FrozenTape CellSparse Packet CellPacketGeometry.LiveWords

/-- The fixed chunk-label count is exactly the live physical reference count
after the row anchors regroup the site words. -/
theorem directory_chunk_count {R B U V O E Q : Type} {a C cap d t : ℕ}
    (S : FrozenTape.Schema R B) (L : FrozenTape.Schema U V) (boxes : Fin a → List (Source.Box O))
    (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
    (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
    (pointer : O → Q) :
    (template S L boxes sh lh priv rep).chunkLabels.length=
      ((directory S L boxes sh lh priv rep args x y cells off box).referenceRows pointer).length := by
  let T := template S L boxes sh lh priv rep
  let owner := cellOf S L x y cells
  let fields := fun i => scalarArgs (cap:=cap) S L x y off box ((roster a S L).get i)
  let D := T.directory owner args fields
  simpa only [directory,T,owner,fields,D,List.length_map] using congrArg List.length
    ((T.chunkLabels_eval owner args fields pointer).trans (D.regroup_owners (anchor S L x y) pointer).symm)

end CellPacketGeometry.History

namespace CellPacketGeometry.History.Native

open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords
open RoutingISA RoutingISA.CellPacket RoutingISA.CellPacket.Supplement RoutingISA.TypedTaskBuilder

variable {O : Type}

/-- The immutable prefix and its last four reserved triples have the full actual
descriptor span, even for the spare cell or an original site with an empty body. -/
theorem CellMemory.descriptor_span {p : Placed O} {geom exclusive : ℕ} {mem : ℕ → ℕ}
    (h : CellMemory p geom exclusive mem) : exclusive=p.descriptorBase+3*(p.parts.length+3) := by
  rw [h.endAddress,CellPacket.descriptors_length,Supplement.prefixChunks,Source.chunks_length]
  simp only [Supplement.prefixParts,Placed.parts,Source.plan,List.length_cons,List.length_append,List.length_map,
    List.length_nil]
  omega

/-- Changing the receiving, scratch, and burst pointers of the typed native row
preserves its entire immutable prepass image at the actual start descriptor. -/
theorem CellMemory.atTask {c geom exclusive : ℕ} {mem : ℕ → ℕ} (l : CellControlRows.Layout)
    (src : ℕ → ℕ) (p : ℕ → Placed O) (h : CellMemory (p c) geom exclusive mem)
    (base : l.sorted+src (l.sorted+l.padded+c)+1=(p c).descriptorBase) :
    CellMemory (l.atCell src p c) geom exclusive mem := by
  refine ⟨?_,h.prefixWords,h.geometry,h.count,?_,?_⟩
  · change WordsAt mem (l.sorted+src (l.sorted+l.padded+c)+1) _
    rw [base]
    exact h.prefixDescriptors
  · change WordsAt mem ((l.sorted+src (l.sorted+l.padded+c)+1)+_) _
    rw [base]
    exact h.tail
  · change exclusive=(l.sorted+src (l.sorted+l.padded+c)+1)+_+12
    rw [base]
    exact h.endAddress

variable {a C pb db dest hdr : ℕ} {E : Type}
    (G : SiteWords.Directory (Fin a) O (C+1)) (ptr : O → E)
    (fit : C+1+G.words.length+(C+1) ≤ 2^pb)
    (space : C+1+(Schema.coords (G.referenceRows ptr).length).length+(C+1) ≤ 2^db)
    (mem : ℕ → ℕ) (slot : O → ℕ) (fs : O → List Factor)
    (ext scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool)
local notation3 (prettyPrint := false) "places" => atRanges (dest:=dest) (H:=hdr) G ptr fit space mem slot fs
  ext scratch burst external
local notation3 (prettyPrint := false) "p" => Terminal.placeAt places
local notation3 (prettyPrint := false) "geometry" => fun c => (p c).publicBase+((Supplement.prefixParts (p c)).flatMap Part.publicBuffer).length
local notation "desc" => descriptorBank dest pb

/-- The public slice for every real or spare slot ends no later than its
descriptor bank. Its payload is a sublist of the first padded rectangle and
the inverse marker rank is a genuine index of that same rectangle. -/
theorem atRanges_public_end
    (rank : ∀ j : Fin (2^pb), mem (dest+(2^pb+j.val))<2^pb) (c : Fin (C+1)) :
    (places c).publicBase+((places c).parts.flatMap Part.publicBuffer).length≤descriptorBank dest pb := by
  have words := congrArg List.length (publicArray G fit c)
  simp only [List.length_map] at words
  have bound : ((places c).parts.flatMap Part.publicBuffer).length≤2^pb := by
    rw [←show ((CellSparse.Packet.Source.plan (G.privateWires c) (G.cellBoxes c) (G.cellRecords c)
      (G.reports c)).flatMap Part.publicBuffer).length=((places c).parts.flatMap Part.publicBuffer).length from rfl,
      ←words]
    exact (List.length_filter_le ..).trans_eq (List.length_finRange)
  have left := rank (Markers.start fit c)
  change dest+mem (dest+(2^pb+(Markers.start fit c).val))+1+_ ≤ dest+(2^pb+2^pb)
  omega

variable (l : CellControlRows.Layout) (src : ℕ → ℕ) (sorted : l.sorted = descriptorBank dest pb)
    (padded : l.padded=2^db) (stops : l.stops=C+1+(Schema.coords (G.referenceRows ptr).length).length)
    (markers : ∀ j : Fin (2^db),
      src (descriptorBank dest pb+(2^db+j.val))=mem (descriptorBank dest pb+(2^db+j.val)))

include sorted padded markers stops in
/-- The native task scans the same descriptor markers as the returned geometry,
including the spare marker. At each reached row it sees all prefix descriptors,
public words, record/report words and reserved triples at the producer's own
rebased addresses. Only the two marker banks need to survive the typed writes. -/
theorem atRanges_produced_memory
    (memory : ∀ c, CellMemory (places c) ((places c).publicBase+((Supplement.prefixParts (places c)).flatMap Part.publicBuffer).length)
      (desc+mem (desc+(2^db+(Markers.stop space c).val))) mem) :
    (∀ c : Fin (C+1), src (l.sorted+l.padded+(l.stops+c.val))-src (l.sorted+l.padded+c.val)-1 =
      3*((places c).parts.length+3)) ∧
    ∀ (i : ℕ) (c : Fin (C+1)), globalCell l.toLayout src i = c.val →
      let owned := Batch.produced l src p geometry (fun _ => []) i
      CellMemory owned.placed owned.geometry (l.sorted+src (l.sorted+l.padded+(l.stops+c.val))) mem := by
  have lo (c : Fin (C+1)) : src (l.sorted+l.padded+c.val)=mem (desc+(2^db+(Markers.start space c).val)) := by
    simpa only [sorted,padded,Nat.add_assoc,Markers.start] using markers (Markers.start space c)
  have hi (c : Fin (C+1)) : src (l.sorted+l.padded+(l.stops+c.val))=mem (desc+(2^db+(Markers.stop space c).val)) := by
    simpa only [sorted,padded,stops,Nat.add_assoc,Markers.stop] using markers (Markers.stop space c)
  have base (c : Fin (C+1)) : l.sorted+src (l.sorted+l.padded+c.val)+1=(places c).descriptorBase := by
    rw [lo,sorted]
    rfl
  constructor
  · intro c
    have h := (memory c).descriptor_span
    rw [←base,←hi,←sorted] at h
    omega
  · intro i c heq owned
    have cast : p c.val=places c := congrArg places (Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ c.isLt)))
    change CellMemory (l.atCell src p (globalCell l.toLayout src i)) (geometry (globalCell l.toLayout src i)) _ _
    rw [heq]
    apply CellMemory.atTask
    · rw [hi,sorted]
      dsimp only
      rw [cast]
      exact memory c
    · rw [cast]
      exact base c

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
