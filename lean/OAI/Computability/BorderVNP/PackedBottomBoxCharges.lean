import OAI.Computability.BorderVNP.PackedBottomBoxLocality
import OAI.Computability.BorderVNP.PackedTableBoundGrid

/-! # The size of the complete original private grid box

Each fine site contributes one original factor. Relocation, zero padding and
report staging occupy linear space in the reserved copy slab. The one-copy
private packet is serialized only once. The visit count multiplies by the
number of actual copies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomRepeat

open Crossing Inherited CellSparse
open scoped Classical

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)
variable (copies capFine stride : ℕ) (box : List Factor)
local notation "s" => bornWith N edges ports v copies capFine stride box

/-- Only the public box reference creates a factor-sweep block. -/
theorem bornWith_blocks : (s).directory.blocks = [⟨0,copies,stride,box⟩] := by
  simp only [Site.directory,Site.rows,bornWith,List.reverse_singleton,List.flatten_cons,List.flatten_nil,
    List.append_nil,List.singleton_append,Directory.blocks,List.filterMap_cons,List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero,Option.getD_some]
  congr 1
  apply List.filterMap_eq_nil_iff.mpr
  intro r hr
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
  rfl

/-- Every copy causes one visit to each factor, including all padding tests. -/
theorem bornWith_visits : (s).directory.visitCount = copies*box.length := by
  simp [Directory.visitCount,bornWith_blocks]

/-- One one-copy factor table and its header are stored for the whole bundle. -/
theorem bornWith_storedMass : Packet.storedMass (s).directory = 1+(box.map Factor.staticMass).sum := by
  simp [Packet.storedMass,Site.directory,bornWith]

/-- Exact sweep syntax mass of the sole repeat block. -/
theorem bornWith_boxMass : (s).directory.boxMass =
    5+box.length+(box.map (fun f => 10000*f.staticMass)).sum := by
  simp [Directory.boxMass,bornWith_blocks,sweepMass]
  omega

/-- The box reference and each real cable or port equality consume constant public syntax. -/
theorem bornWith_recordMass : (s).directory.recordMass = 1+1025*(1+Fintype.card (Row N v)) := by
  have hr : (ties N edges ports v copies capFine stride).map Record.guardMassBound =
      List.replicate (Fintype.card (Row N v)) 1024 := by
    simp [ties,List.map_map,Function.comp_def,tie,Record.guardMassBound]
  simp [Directory.recordMass,Site.directory,Site.rows,bornWith,Record.guardMassBound,hr,Nat.mul_add,Nat.mul_comm]
  omega

end Packing.BottomRepeat

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports BottomRepeat Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)
variable (capFine capReport : ℕ)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "sz" => bottomStride (capFine+incoming G v) capReport
local notation "box" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID
  groupID v rules capFine capReport
local notation "sites" => Fintype.card {u : N.Site // cell u = v}
local notation "s" => born N cell position pack width owner lane aligned siteID edgeID portID channelID
  groupID v rules

include channelID groupID in
omit [Fintype P] in
private theorem channelVolume :
    Fintype.card {q : Q // src q = v ∨ dst q = v} * H ≤ incoming G v := by
  let tag (l : GridPadding.LocalLane (N := N.cellNetwork cell position) (src := src) (dst := dst) (H := H) v) :
      InputLane G v := .inl ⟨l.1,l.2⟩
  have hinj : Function.Injective tag := by
    rintro ⟨q,i⟩ ⟨r,k⟩ e
    dsimp only [tag] at e
    cases Sum.inl.inj e
    rfl
  have h := Fintype.card_le_of_injective _ ((sourceOrder G channelID groupID v).injective.comp hinj)
  simpa only [GridPadding.LocalLane,Fintype.card_prod,Fintype.card_fin] using h

/-- Every fine site, including a selected source, occupies one factor. The
additional private rows fit within the copy capacity and its incident words. -/
theorem stored_length_le (hf : GridBoxes.stride N cell v ≤ capFine) :
    (box).length ≤ sites+sz := by
  have hp := (GridPadding.factors_length_le pack v
    (channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v capFine)).trans
    (channelVolume N cell position width owner channelID groupID v)
  simp only [stored,wiring,List.length_append,stage_length,factors,List.length_map,siteList_length,
    fineTies,List.length_ofFn,fineZeros,List.length_range,reportZeros,bottomStride]
  change guessedSize N cell v + suppliedSize N cell v ≤ capFine at hf
  unfold GridBoxes.stride
  omega

private theorem stage_truth (next : ℕ) (rows : List Factor)
    (h : ∀ f ∈ rows, (∃ ws rs, f = .truth ws rs) ∨ ∃ i t, f = .unary i t) :
    ∀ f ∈ stage next rows, ∃ ws rs, f = .truth ws rs := by
  induction rows generalizing next with
  | nil => simp [stage]
  | cons f fs ih =>
    obtain ⟨hf,hs⟩ := List.forall_mem_cons.mp h
    rcases hf with ⟨ws,rs,rfl⟩ | ⟨i,t,rfl⟩
    · exact List.forall_mem_cons.mpr ⟨⟨ws,rs,rfl⟩,ih _ hs⟩
    · exact List.forall_mem_cons.mpr ⟨⟨_,_,rfl⟩,ih _ hs⟩

/-- Even the originally weighted source is represented here by a relative
Boolean comparison against its separately reported use bit. -/
theorem stored_truth : ∀ f ∈ box, ∃ ws rs, f = .truth ws rs := by
  simp only [stored,wiring,List.forall_mem_append]
  refine ⟨⟨stage_truth _ _ ?_,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩
  · intro f hf
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hf
    cases h : rules u
    · exact Or.inl ⟨_,_,rfl⟩
    · exact Or.inr ⟨_,_,rfl⟩
  · intro f hf; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hf; exact ⟨_,_,rfl⟩
  all_goals intro f hf; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hf; exact ⟨_,_,rfl⟩

private theorem bound_sum {α : Type} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ B*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih fun a ha => h a (.tail _ ha)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

/-- Actual one-copy storage mass, expanded visit count, and private sweep mass,
charged to the same trivalent fine sites and their true work stride. -/
theorem born_charges (copies : ℕ) (hf : GridBoxes.stride N cell v ≤ capFine)
    (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3) :
    let site := s copies capFine capReport
    Packet.storedMass site.directory ≤ 1+81*(sites+sz) ∧
      site.directory.boxMass ≤ 5+810001*(sites+sz) ∧ site.directory.visitCount ≤ copies*(sites+sz) := by
  have htable := born_tableBound N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules copies capFine capReport degree
  have hl := stored_length_le N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules capFine capReport hf
  have hmass (f) (h : f ∈ box) : f.staticMass ≤ 81 := by
    have ht := htable box List.mem_cons_self f h
    obtain ⟨ws,rs,rfl⟩ := stored_truth N cell position pack width owner lane aligned siteID edgeID
      portID channelID groupID v rules capFine capReport f h
    exact Nat.mul_le_mul (Nat.succ_le_succ ht.1) (Nat.succ_le_succ ht.2)
  have h1 := bound_sum box Factor.staticMass 81 hmass
  have h2 := bound_sum box (fun f => 10000*f.staticMass) 810000
    (fun f h => Nat.mul_le_mul_left 10000 (hmass f h))
  dsimp only
  change Packet.storedMass (bornWith G channelID groupID v copies capFine sz box).directory ≤ _ ∧ _
  rw [bornWith_storedMass]
  refine ⟨by omega,?_,?_⟩
  · change (bornWith G channelID groupID v copies capFine sz box).directory.boxMass ≤ _
    rw [bornWith_boxMass]
    omega
  · exact (bornWith_visits G channelID groupID v copies capFine sz box).le.trans (Nat.mul_le_mul_left _ hl)

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
