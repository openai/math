import OAI.Computability.BorderVNP.CellPacketTypedInitializer
import OAI.Computability.BorderVNP.CellPacketSourceSize

/-! # Sparse resource bounds for the physical private-cell initializer

The geometry contributes one machine word per public field. Each original site
contributes its length header and a single bounded description, independently of
the number of times the private macro refers to it. The external assignment
contributes one bit per wire. These quantities bound the native ticks, scratch
addresses, and physical words passed to the private call.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellSparse CellSparse.Packet.Source RationalHitting.StackLanguage

variable {Site : Type} {w : ℕ}

/-- Public word scans, descriptor visits, original descriptions (including their header),
and the actual number of external inputs, in the schedule of a placed cell. -/
def Placed.units (p : Placed Site) (w description : ℕ) : ℕ :=
  (w+1)*((p.parts.flatMap Part.publicBuffer).length+p.parts.length+1) +
    (description+1)*(privateKeys p.parts).length + p.external.length

/-- In the concrete plan there are two fixed public blocks and one part per box ordinal.
Only original-site box ordinals contribute private descriptions. -/
theorem Placed.units_plan (p : Placed Site) (w description : ℕ) :
    p.units w description =
      (w+1)*((p.parts.flatMap Part.publicBuffer).length+p.boxes.length+3) +
        (description+1)*(p.boxes.filterMap Sum.getRight?).length + p.external.length := by
  have h : p.parts.length = p.boxes.length+2 := by simp [Placed.parts,plan]
  have k := privateKeys_plan p.privateWires p.boxes p.rows p.reports
  change privateKeys p.parts = p.boxes.filterMap Sum.getRight? at k
  rw [Placed.units,h,k]
  ring

/-- The encoded sparse packet itself, before the external bank and enclosing field markers.
All public scalar magnitudes are bounded by their actual physical word values. -/
theorem Placed.packet_length_le (p : Placed Site) (m : Memory w) (description : ℕ)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer)) :
    p.task.packet.length ≤
      (2*w+2)*(p.parts.flatMap Part.publicBuffer).length + description*(privateKeys p.parts).length :=
  chunks_bits_length_le m p.slot p.headerWidth description p.factors p.parts p.publicBase room words

/-- The same estimate on the generator's actual typed input packet. -/
theorem Placed.typed_packet_length_le (p : Placed Site) (m : Memory w) (description : ℕ)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer)) :
    (CellSparse.Packet.bits p.directory p.privateWires).length ≤
      (2*w+2)*(p.parts.flatMap Part.publicBuffer).length + description*(privateKeys p.parts).length := by
  have eq : p.task.packet = CellSparse.Packet.bits p.directory p.privateWires :=
    packet_bits p.slot p.headerWidth p.factors p.privateWires p.boxes p.rows p.reports p.publicBase
  rw [←eq]
  exact p.packet_length_le m description room words

/-- The actual native initializer fits 300 ticks per sparse resource unit. -/
theorem Placed.cost_le (p : Placed Site) (m : Memory w) (description : ℕ)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer)) :
    p.task.cost w ≤ 300*p.units w description := by
  have packetBound := p.packet_length_le m description room words
  have work := chunks_work_total_le p.slot p.headerWidth description w p.factors p.parts p.publicBase room
  have n : p.task.chunks.length = p.parts.length := chunks_length p.slot p.headerWidth p.factors p.parts p.publicBase
  change (p.task.chunks.map (Chunk.work w)).sum ≤ _ at work
  have f := finishCost_le p.task.packet p.external
  change chunksCost w p.task.chunks + finishCost p.task.packet p.external ≤ _
  rw [chunksCost_eq,n]
  unfold Placed.units
  nlinarith only [work, f, packetBound, Nat.zero_le (w*(p.parts.flatMap Part.publicBuffer).length),
    Nat.zero_le (w*p.parts.length), Nat.zero_le (description*(privateKeys p.parts).length)]

/-- One scratch word holds one enclosing-field or external bit. -/
theorem Placed.scratch_length_le (p : Placed Site) (m : Memory w) (description : ℕ)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer)) :
    p.task.payload.length ≤ 4*p.units w description := by
  have packetBound := p.packet_length_le m description room words
  change (codeWord p.task.packet ++ p.external).length ≤ _
  rw [List.length_append,codeWord_length]
  unfold Placed.units
  nlinarith only [packetBound, Nat.zero_le (w*p.parts.length), Nat.zero_le (description*(privateKeys p.parts).length)]

/-- The burst occupies the quotient of the framed payload size by machine width, plus
one final word containing its terminator and padding. -/
theorem Placed.burst_length_le (p : Placed Site) (m : Memory w) (description : ℕ) (hw : 0 < w)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer)) :
    (p.task.burst w).length ≤ (8*p.units w description)/w+1 := by
  have size := p.scratch_length_le m description room words
  rw [Task.burst, CompactFrame.length_pack, ← CompactFrame.wordCount, CompactFrame.wordCount_terminator hw]
  exact Nat.succ_le_succ (Nat.div_le_div_right (by omega))

/-- Publicly reserved scratch and burst intervals imply the exact room assumptions of the
physical initializer, uniformly over all private descriptions of the stated size. -/
theorem Placed.room_of_reservation (p : Placed Site) (m : Memory w) (description : ℕ) (hw : 0 < w)
    (body : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer))
    (chunkEnd : ∀ c ∈ p.task.chunks, c.endSource ≤ p.scratchBase)
    (tableEnd : p.descriptorBase+3*p.parts.length ≤ p.scratchBase)
    (externalApart : CompactWrite.Disjoint p.externalBase p.external.length p.scratchBase (4*p.units w description))
    (burstApart : CompactWrite.Disjoint p.scratchBase (4*p.units w description) p.burstBase ((8*p.units w description)/w+1))
    (sourceFit : p.externalBase+p.external.length < 2^w)
    (scratchFit : p.scratchBase+4*p.units w description < 2^w)
    (burstFit : p.burstBase+((8*p.units w description)/w+1) ≤ 2^w)
    (countFit : (8*p.units w description)/w+1 < 2^w) : p.task.Room w := by
  have scratch := p.scratch_length_le m description body words
  have burst := p.burst_length_le m description hw body words
  have n : p.task.chunks.length = p.parts.length := chunks_length p.slot p.headerWidth p.factors p.parts p.publicBase
  refine ⟨hw,chunkEnd,?_,?_,?_,sourceFit,?_,?_,burst.trans_lt countFit⟩
  · rw [n]; exact tableEnd
  · change p.externalBase+p.external.length ≤ p.scratchBase ∨ p.scratchBase+p.task.payload.length ≤ p.externalBase
    rcases externalApart with h | h <;> omega
  · change p.scratchBase+p.task.payload.length ≤ p.burstBase ∨ p.burstBase+(p.task.burst w).length ≤ p.scratchBase
    rcases burstApart with h | h <;> omega
  · change p.scratchBase+p.task.payload.length < 2^w; omega
  · change p.burstBase+(p.task.burst w).length ≤ 2^w; omega

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
