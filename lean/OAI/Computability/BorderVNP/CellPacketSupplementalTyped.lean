import OAI.Computability.BorderVNP.CellPacketTypedInitializer
import OAI.Computability.BorderVNP.CellPacketSupplementalNative

/-! # Combining public geometry records with original-site supplemental checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement

open VPVNP.BurstRAM CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketEncode (packet)
open private chunks_bits box_parts frame_append from OAI.Computability.BorderVNP.CellPacketSources

variable {Site : Type}

/-- The compact typed counts used by the fixed prepass. -/
def measured (geomBase : ℕ) (geom extra : List Record) : Data :=
  ⟨geomBase,geom.length,(geom.flatMap record).length,extra.length,(extra.flatMap record).length⟩

/-- Geometry-supplied header words and one-copy boxes, ending before the record count. -/
def prefixParts (p : Placed Site) : List (CellSparse.Packet.Source.Part Site) :=
  .publicWords [p.privateWires,p.boxes.length] :: p.boxes.map boxPart

/-- The fixed prefix keeps the same raw descriptor addresses when the number of
private supplemental rows varies. -/
def prefixChunks (p : Placed Site) : List Chunk :=
  chunks p.slot p.headerWidth p.factors p.publicBase (prefixParts p)

/-- The four native source intervals for the combined record count, ordinary rows,
supplemental rows and public report words, in private generator order. -/
def tailChunks (l : Layout) (p : Placed Site) (geomBase : ℕ) (extra : List Record) : List Chunk :=
  [.words l.merged [p.rows.length+extra.length],
   .words (geomBase+1) (p.rows.flatMap record),.words l.supplement (extra.flatMap record),
   .words (geomBase+1+(p.rows.flatMap record).length) (fieldList vector p.reports)]

/-- The initializer ABI stays fixed. Only the four reserved final source intervals
change after the true sidecar measurements become available. -/
def task (l : Layout) (p : Placed Site) (geomBase : ℕ) (extra : List Record) : Task :=
  {p.task with chunks := prefixChunks p ++ tailChunks l p geomBase extra}

/-- The actual four descriptors emitted by the native arithmetic routine select
the required typed data intervals. -/
theorem tail_descriptors (l : Layout) (p : Placed Site) (geomBase : ℕ) (extra : List Record)
    (reports : l.reportWords = (fieldList vector p.reports).length) :
    CellPacket.descriptors (tailChunks l p geomBase extra) = descriptors l (measured geomBase p.rows extra) := by
  simp [CellPacket.descriptors,tailChunks,Chunk.descriptor,descriptors,measured,reports]

/-- The complete spliced argument is the exact typed private program with all
site-dependent checks after the geometry records. In particular the true merged
record count is encoded even when the sidecar has variable length. -/
theorem payload_eq (l : Layout) (p : Placed Site) (geomBase : ℕ) (extra : List Record) :
    (task l p geomBase extra).payload =
      CellSparse.Packet.input {p.directory with records := p.rows++extra} p.privateWires p.external := by
  apply congrArg (fun xs => RationalHitting.StackLanguage.codeWord xs ++ p.external)
  change ((prefixChunks p ++ tailChunks l p geomBase extra).flatMap Chunk.bits) = _
  rw [List.flatMap_append,prefixChunks,chunks_bits]
  simp only [prefixParts,List.flatMap_cons,Part.denote,box_parts,tailChunks,List.flatMap_nil,List.append_nil,Chunk.bits]
  simp only [←frame_append,CellSparse.Packet.bits,CellSparse.Packet.words,fieldList,Placed.directory,
    List.length_append,List.flatMap_append,List.length_map,List.cons_append,List.nil_append,List.append_assoc]
  rfl

end RoutingISA.CellPacket.Supplement

end BorderVNP
end Computability
end OAI
