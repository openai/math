import OAI.Computability.BorderVNP.CellPacketGeometryRecordPositions

/-! # Public gate and word costs of the frozen row decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket.Stored

open Inherited CellSparse Word
open private routeTags from OAI.Computability.BorderVNP.CellPacketGeometryRecordTags
open private portAt routeAt from OAI.Computability.BorderVNP.CellPacketGeometryRecordPositions
open private portWords routeWords from OAI.Computability.BorderVNP.PackedBankPacket

variable {I : Type*}

private theorem shape_words_length (s : Shape) (f : ℕ → WidthExpr I) :
    (s.code f).words.length = s.tags.length := by
  cases s with
  | zero | equal | box => rfl
  | profile h r =>
    simp [Shape.code,RecordCode.words,Shape.tags,routeTags,portWords,routeWords,portAt,routeAt,
      List.length_flatMap,Function.comp_def]

/-- The original frozen scalar stream emits exactly one public word per legal
relocation tag, including both address words of every compact profile route. -/
theorem fromTags_length_legal (s : Shape) (pin : Fin s.tags.length → I) :
    (fromTags s.tags pin).words.length = s.tags.length := by
  rw [fromTags,decode_tags,shape_words_length]

/-- Even an inactive or malformed slot has a linear decoded word reservation.
The inferred route count is bounded by the number of supplied address tags. -/
theorem fromTags_length_le (ts : List Kind) (pin : Fin ts.length → I) :
    (fromTags ts pin).words.length ≤ 9*(ts.length+1) := by
  rw [fromTags,shape_words_length]
  unfold decodeShape
  split
  · change 5 ≤ _; omega
  · split
    · have hc := List.count_le_length (a := Kind.bitAddress) (l := ts)
      simp [Shape.tags,routeTags,Nat.mul_comm]
      omega
    · split <;> first | change 6 ≤ _; omega | change 9 ≤ _; omega

private theorem field_nodes (ts : List Kind) (pin : Fin ts.length → I) (j : ℕ) :
    (fieldOf ts pin j).nodes = 1 := by
  unfold fieldOf
  split <;> rfl

private theorem shape_nodes (s : Shape) (f : ℕ → WidthExpr I) (nodes : ∀ i, (f i).nodes=1) :
    ∀ e ∈ (s.code f).words, e.nodes=1 := by
  cases s <;>
    simp [Shape.code,RecordCode.words,portWords,routeWords,portAt,routeAt,WidthExpr.nodes,nodes]
  intro e he
  rcases he with ⟨i,rfl⟩ | rfl | ⟨i,hi⟩
  · exact nodes _
  · rfl
  · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact nodes _

/-- Every original immutable scalar compiles to a single field or constant leaf. -/
theorem fromTags_nodes (ts : List Kind) (pin : Fin ts.length → I) :
    ∀ e ∈ (fromTags ts pin).words, e.nodes=1 :=
  shape_nodes _ _ (field_nodes ts pin)

/-- Placing the final bit and box offsets preserves the serialized row length. -/
theorem placed_words_length (r : RecordCode I) (off box : WidthExpr I) :
    (r.placed off box).words.length = r.words.length := by
  rw [RecordCode.placed_words,←markedCode_words r]
  simp only [List.length_map]

/-- Final placement uses at most one binary addition with a shared offset leaf
for each frozen scalar. This includes private-box identifiers and route ends. -/
theorem placed_fromTags_nodes (ts : List Kind) (pin : Fin ts.length → I) (off box : I) :
    ∀ e ∈ ((fromTags ts pin).placed (.field off) (.field box)).words, e.nodes≤3 := by
  rw [RecordCode.placed_words]
  rintro e he
  obtain ⟨⟨k,v⟩,hm,rfl⟩ := List.mem_map.mp he
  have mem : v ∈ (fromTags ts pin).words := by
    rw [←markedCode_words]
    exact List.mem_map_of_mem hm
  simpa only [fromTags_nodes ts pin v mem] using moved_nodes off box k v

end Packing.BankPacket.Stored

end BorderVNP
end Computability
end OAI
