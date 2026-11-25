import OAI.Computability.BorderVNP.PackedGridSeedTape
import OAI.Computability.BorderVNP.PackedBottomBoxScalars
import OAI.Computability.BorderVNP.PackedFrozenBottomRows

/-! # The actual public frozen directory at the routed seed

The repeated box and its public incidence ties have the same static integers
for every hidden route choice and one-copy factor list. Their site and wire
names come solely from the finite directed deck grid. A loop contributes a
single incident cable row, and each tile has one attached grouped port.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Seed

open Crossing Cover DeckGrid CellSparse BottomRepeat BottomReports InheritedBank Diagonal.ExternalSew
open scoped Classical
variable {D q depth : ℕ} (n r : ℕ)
local notation "V₀" => Fin q → Deck (depth+2)
local notation "T₀" => GridHosts.tileCount q depth
/-- The same equality used to enumerate the deck-grid incidence subtypes. -/
noncomputable local instance publicDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
variable (order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2)))
variable (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The public padded Cayley grid with its unique grouped port on each tile.
Its definition does not take a verifier witness or a stored private table. -/
noncomputable abbrev layout : Network D (Fin T₀) (fun _ => GridHosts.inputBlockWidth r n q depth) where
  Site := V₀
  Edge := V₀ × Direction q
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Prod.fst
  dst e := e.1 * step q (depth+2) e.2
  width _ := seedChannelWidth n r q depth
  attach := order
  position v := (position v).val
  in_ball v := (position v).property

variable {qe qa : ℕ} (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe) (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (copies : ℕ)
local notation "G₀" => layout n r order position
local notation "S₀" => seedSiteCapacity n r q depth
local notation "K₀" => seedBoxCapacity n r q depth (Fintype.card (Direction q))

/-- True one-copy work stride of the public tile, including both padding areas. -/
noncomputable def stride (c : V₀) := bottomStride (3*S₀+incoming G₀ c) S₀

/-- The actual public birth directory, containing one five-field reference
and all nine-field ties in the evaluator's order. -/
noncomputable def rows (c : V₀) : List Record :=
  .box 0 0 copies (stride n r order position c) :: ties G₀ channels groups c copies (3*S₀) (stride n r order position c)

private theorem attached_card (c : V₀) : Fintype.card (Attached G₀ c) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨order.symm c,order.apply_symm_apply _⟩,fun j => Subtype.ext
    (order.injective (j.property.trans (order.apply_symm_apply c).symm))⟩

/-- Exactly one record for the box, one for the grouped port, and one per
distinct incident directed channel. -/
theorem rows_length (c : V₀) :
    (rows n r order position channels groups copies c).length = 2+Fintype.card (Incident G₀ c) := by
  have ha := attached_card n r order position c
  simp only [rows,List.length_cons,ties_length,Row,Fintype.card_sum,ha]
  omega

/-- At most two incident records per direction; coincident endpoints share
one row of the real grid. -/
theorem rows_length_le (c : V₀) :
    (rows n r order position channels groups copies c).length ≤ 2+2*Fintype.card (Direction q) := by
  rw [rows_length]
  exact Nat.add_le_add_left (GridPadding.cayley_ends (step q (depth+2)) c) 2

/-- Exact scalar field count of an arbitrary stored birth row, including its opcode. -/
theorem row_fields (c : V₀) (u : Record) (hu : u ∈ rows n r order position channels groups copies c) :
    (marked u).length = 5 ∨ (marked u).length = 9 := by
  rcases List.mem_cons.mp hu with rfl | h
  · exact Or.inl rfl
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    exact Or.inr rfl

/-- Repetition scales the entire canonical incoming slab by the number of
copies, including local loops and zero-width inputs. -/
theorem incoming_wide (c : V₀) : incoming (wide G₀ copies) c = copies*incoming G₀ c := by
  rw [incoming_eq_widths,incoming_eq_widths,Nat.mul_add]
  unfold incidentWidth portWidth
  rw [Finset.mul_sum,Finset.mul_sum]

/-- The public stride fits the same cap paid by the real private site. -/
theorem stride_le (c : V₀) : stride n r order position c ≤ K₀ := by
  have ha := attached_card n r order position c
  have hi : Fintype.card (Incident G₀ c) ≤ 2*Fintype.card (Direction q) := GridPadding.cayley_ends _ c
  have inc : incoming G₀ c = Fintype.card (Incident G₀ c)*seedChannelWidth n r q depth+
      GridHosts.inputBlockWidth r n q depth := by
    rw [incoming_eq_widths]
    change (∑ _ : Incident G₀ c, seedChannelWidth n r q depth) +
      (∑ _ : Attached G₀ c,GridHosts.inputBlockWidth r n q depth) = _
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,ha,one_mul]
  have he := Nat.mul_le_mul_right (seedChannelWidth n r q depth) hi
  unfold stride bottomStride seedBoxCapacity
  rw [inc]
  omega

/-- Uniform largest stored scalar. It covers the single-copy stride and copy
multiplicity even when the expanded area of an empty bundle is zero. -/
noncomputable def scalarCap (n r q depth copies : ℕ) :=
  let K := seedBoxCapacity n r q depth (Fintype.card (Direction q))
  max 2 (max copies (max K (2*copies*K)))

/-- Every scalar actually present in this site's public frozen tape fits the
published uniform bound, including all bases of empty incidence rows. -/
theorem scalar_le (c : V₀) (u : Record) (hu : u ∈ rows n r order position channels groups copies c)
    (z : Kind × ℕ) (hz : z ∈ marked u) : z.2 ≤ scalarCap n r q depth copies := by
  let d := stride n r order position c
  let s := bornWith G₀ channels groups c copies (3*S₀) d []
  have h := bornWith_scalarBound G₀ channels groups c copies (3*S₀) d [] (Nat.le_add_right _ _)
  have hm : z ∈ s.markedWords := List.mem_flatMap.mpr ⟨u,by simpa [s,bornWith,Site.rows,rows,d] using hu,hz⟩
  have bound := h z hm
  change z.2 ≤ max 2 (max copies (max d (copies*d+incoming (wide G₀ copies) c))) at bound
  have hd := stride_le n r order position c
  have hinc : incoming G₀ c ≤ d := by unfold d stride bottomStride; omega
  rw [incoming_wide] at bound
  have h1 := Nat.mul_le_mul_left copies hd
  have h2 := Nat.mul_le_mul_left copies (hinc.trans hd)
  change z.2 ≤ max 2 (max copies (max K₀ (2*copies*K₀)))
  rw [Nat.mul_assoc]
  change d ≤ K₀ at hd
  change copies*d ≤ copies*K₀ at h1
  omega

local notation "rs₀" => rows n r order position channels groups copies
local notation "C₀" => scalarCap n r q depth copies

/-- A wider common production word can be used by the complete history frame. -/
theorem fits_of_width {width : ℕ} (room : C₀ < 2^width) : Bottom.Fits rs₀ width :=
  fun c u hu z hz => (scalar_le n r order position channels groups copies c u hu z hz).trans_lt room

/-- The binary size of the uniform scalar cap is a sufficient actual producer width. -/
theorem fits : Bottom.Fits rs₀ (C₀).size :=
  fits_of_width n r order position channels groups copies (Nat.lt_size_self _)

/-- Total number of real frozen birth records across the grid, including any
explicit disabled reservations supplied by the caller. -/
theorem row_slots (holes : ℕ) : Fintype.card (Bottom.Row rs₀ holes) ≤
    T₀*(2+2*Fintype.card (Direction q))+holes := by
  rw [Bottom.card_rows]
  apply Nat.add_le_add_right
  apply (Finset.sum_le_sum (fun c _ => rows_length_le n r order position channels groups copies c)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]

/-- The frozen scalar-bit directory stores at most nine words per real row.
Disabled reservations contribute no payload bits, for any width. -/
theorem payload_slots (holes width : ℕ) : Fintype.card (Bottom.Payload rs₀ holes width) ≤
    T₀*(2+2*Fintype.card (Direction q))*9*width := by
  rw [Bottom.card_payload]
  apply Nat.mul_le_mul_right
  rw [Fintype.sum_sum_type]
  simp only [Bottom.fields, List.length_nil,Finset.sum_const_zero,Nat.add_zero]
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (a : Σ c, Fin (rs₀ c).length) _ => show (marked (rs₀ a.1)[a.2.val]).length ≤ 9 from by
      have h := row_fields n r order position channels groups copies a.1 _ (List.getElem_mem a.2.isLt)
      omega)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at hh
  apply hh.trans
  apply Nat.mul_le_mul_right
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simpa only [Bottom.card_rows,Nat.add_zero] using row_slots n r order position channels groups copies 0

/-- All emitted output pins of the real leaf frame, counting every live bit,
owner field, disabled slot, and immutable scalar bit. -/
theorem pin_count (holes width ownerWidth : ℕ) :
    Fintype.card (Pins (Bottom.Row rs₀ holes) (Bottom.Payload rs₀ holes width) ownerWidth) ≤
      (T₀*(2+2*Fintype.card (Direction q))+holes)*(1+ownerWidth)+
        T₀*(2+2*Fintype.card (Direction q))*9*width := by
  have eq : Fintype.card (Pins (Bottom.Row rs₀ holes) (Bottom.Payload rs₀ holes width) ownerWidth) =
      Fintype.card (Bottom.Row rs₀ holes)*(1+ownerWidth)+Fintype.card (Bottom.Payload rs₀ holes width) := by
    simp only [Pins,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin]
  rw [eq]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (row_slots n r order position channels groups copies holes))
    (payload_slots n r order position channels groups copies holes width)

/-- Two shared constant gates suffice to produce all owners, active bits and
frozen scalar bits for the published bottom grid. -/
theorem frame_size {σ : Type*} [Fintype σ] (holes width : ℕ) {d : ℕ} (id : V₀ ↪ Fin (2^d)) :
    (Bottom.frame (σ := σ) rs₀ holes width id).size ≤ 2 := Bottom.frame_size ..

end Packing.Inherited.FrozenTape.Seed

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse Cover GridPlacement BottomReports BottomGridBank Inherited Inherited.FrozenTape
open Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire TeamContraction VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin s) (edges : (W.routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (copies : ℕ)

local notation "site₀" => fun c => W.seedBorn position code sites edges ports channels groups c copies
local notation "rs₀" => Seed.rows n r order position channels groups copies
local notation "w₀" => Nat.size (Seed.scalarCap n r q depth copies)

/-- The native site's public history consists exactly of the static deck-grid
rows, with no dependence on its opaque one-copy description. -/
theorem seedBorn_frozen_rows (c : Fin q → Deck (depth+2)) :
    ((site₀) c).rows = rs₀ c := by
  simp only [seedBorn,born,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,
    List.append_nil,List.singleton_append]
  rfl

/-- The bottom leaf frame fits directly into a caller's wider common word
format and satisfies the complete frozen-directory image on that format. -/
theorem seedBorn_frozen_image_at_width {σ : Type*} [Fintype σ] {ownerWidth width : ℕ}
    (id : (Fin q → Deck (depth+2)) ↪ Fin (2^ownerWidth)) (holes : ℕ) (x : σ → Bool)
    (room : Seed.scalarCap n r q depth copies < 2^width) :
    (Bottom.schema rs₀ holes width).Image ((Bottom.frame rs₀ holes width id).eval x)
      (id.trans Fin.valEmbedding) (site₀) :=
  Bottom.image rs₀ holes width id (Seed.fits_of_width n r order position channels groups copies room)
    x (site₀) (W.seedBorn_frozen_rows position code sites edges ports channels groups copies)

/-- The shared Boolean constant frame emits the actual marked field words
and site owners of every physical bottom birth. -/
theorem seedBorn_frozen_image {σ : Type*} [Fintype σ] {ownerWidth : ℕ}
    (id : (Fin q → Deck (depth+2)) ↪ Fin (2^ownerWidth)) (holes : ℕ) (x : σ → Bool) :
    (Bottom.schema rs₀ holes w₀).Image ((Bottom.frame rs₀ holes w₀ id).eval x)
      (id.trans Fin.valEmbedding) (site₀) :=
  W.seedBorn_frozen_image_at_width position code sites edges ports channels groups copies id holes x
    (Nat.lt_size_self _)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
