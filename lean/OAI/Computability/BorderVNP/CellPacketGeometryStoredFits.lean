import OAI.Computability.BorderVNP.CellPacketGeometryStoredCost

/-! # Arithmetic width of the positional frozen-row decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket.Stored

open Inherited CellSparse Word
open private portAt routeAt from OAI.Computability.BorderVNP.CellPacketGeometryRecordPositions
open private portWords routeWords from OAI.Computability.BorderVNP.PackedBankPacket

variable {I : Type*} {w : ℕ}

private theorem nodes_pos (e : WidthExpr I) : 0<e.nodes := by cases e <;> simp [WidthExpr.nodes]

private theorem leaf_fits (e : WidthExpr I) (x : I → ℕ) (leaf : e.nodes=1) :
    e.Fits w x ↔ e.eval x < 2^w := by
  cases e with
  | const | field => rfl
  | binary op l r =>
    have := nodes_pos l
    simp only [WidthExpr.nodes] at leaf
    omega

private theorem shape_bounded (s : Shape) (f : ℕ → WidthExpr I) (x : I → ℕ)
    (operands : ∀ i, (f i).eval x < 2^w) (three : 3<2^w)
    (arities : ∀ h r, s=.profile h r → h<2^w ∧ r<2^w) :
    ∀ e ∈ (s.code f).words, e.eval x < 2^w := by
  have h₀ : 0 < 2^w := by omega
  have h₁ : 1 < 2^w := by omega
  have h₂ : 2 < 2^w := by omega
  cases s with
  | zero | equal | box =>
    simp [Shape.code,RecordCode.words,portAt,portWords,WidthExpr.eval,operands,h₁,h₂]
  | profile h r =>
    obtain ⟨hh,hr⟩ := arities h r rfl
    simp [Shape.code,RecordCode.words,portAt,portWords,routeAt,routeWords,WidthExpr.eval,three,operands,hh]
    intro e he
    rcases he with ⟨j,rfl⟩ | rfl | ⟨j,hj⟩
    · exact operands _
    · exact hr
    · rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact operands _

private theorem decoded_arities (ts : List Kind) (h r : ℕ) (eqn : decodeShape ts = .profile h r) :
    h ≤ ts.length ∧ r ≤ ts.length := by
  unfold decodeShape at eqn
  split at eqn
  · cases eqn
  · split at eqn
    · cases eqn
      have := List.count_le_length (a := Kind.bitAddress) (l := ts)
      omega
    · split at eqn <;> cases eqn

/-- Decoding any tag stream reads bounded input fields and bounded constructor
constants. The fallback for malformed tags has the same width bound. -/
theorem fromTags_bounded (ts : List Kind) (pin : Fin ts.length → I) (x : I → ℕ)
    (inputs : ∀ j, x (pin j) < 2^w) (three : 3<2^w) (len : ts.length < 2^w) :
    ∀ e ∈ (fromTags ts pin).words, e.eval x < 2^w := by
  apply shape_bounded
  · intro i
    unfold fieldOf
    split
    · exact inputs _
    · exact Nat.two_pow_pos _
  · exact three
  · intro h r eqn
    obtain ⟨hh,hr⟩ := decoded_arities ts h r eqn
    exact ⟨hh.trans_lt len,hr.trans_lt len⟩

/-- An unplaced row consists of leaves, so its bounded evaluated words fit at
every intermediate arithmetic node. -/
theorem fromTags_word_fits (ts : List Kind) (pin : Fin ts.length → I) (x : I → ℕ)
    (inputs : ∀ j, x (pin j) < 2^w) (three : 3<2^w) (len : ts.length < 2^w) :
    ∀ e ∈ (fromTags ts pin).words, e.Fits w x := fun e he =>
  (leaf_fits e x (fromTags_nodes ts pin e he)).mpr (fromTags_bounded ts pin x inputs three len e he)

/-- Each relocated word is a leaf or one addition of two nonnegative leaves.
A bound on its actual serialized value therefore bounds all of its intermediates. -/
theorem placed_word_fits (ts : List Kind) (pin : Fin ts.length → I) (off box : I) (x : I → ℕ)
    (e : WidthExpr I) (he : e ∈ ((fromTags ts pin).placed (.field off) (.field box)).words)
    (output : e.eval x < 2^w) : e.Fits w x := by
  rw [RecordCode.placed_words] at he
  obtain ⟨⟨k,v⟩,hm,rfl⟩ := List.mem_map.mp he
  have hv : v ∈ (fromTags ts pin).words := by rw [←markedCode_words]; exact List.mem_map_of_mem hm
  have leaf := leaf_fits (w := w) v x (fromTags_nodes ts pin v hv)
  cases k <;> simp only [moved,WidthExpr.eval,WidthExpr.Fits,Op.apply,leaf] at output ⊢ <;> omega

/-- Zero offsets leave every evaluated scalar at its unplaced value. Inactive
slots thus need only the original raw word and immutable schema widths. -/
theorem placed_zero_fits (ts : List Kind) (pin : Fin ts.length → I) (off box : I) (x : I → ℕ)
    (hz : x off=0) (hb : x box=0) (inputs : ∀ j, x (pin j)<2^w) (three : 3<2^w) (len : ts.length<2^w) :
    ∀ e ∈ ((fromTags ts pin).placed (.field off) (.field box)).words, e.Fits w x := by
  intro e he
  apply placed_word_fits _ _ _ _ _ e he
  rw [RecordCode.placed_words] at he
  obtain ⟨⟨k,v⟩,hm,rfl⟩ := List.mem_map.mp he
  have hv : v ∈ (fromTags ts pin).words := by rw [←markedCode_words]; exact List.mem_map_of_mem hm
  cases k <;> simpa only [moved,WidthExpr.eval,Op.apply,hz,hb,Nat.zero_add] using
    fromTags_bounded ts pin x inputs three len v hv

end Packing.BankPacket.Stored

end BorderVNP
end Computability
end OAI
