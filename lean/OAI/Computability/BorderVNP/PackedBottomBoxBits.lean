import OAI.Computability.BorderVNP.PackedBottomBoxCharges

/-! # The transmitted private bit string of an original grid site

The box body uses the actual scalar encoding consumed by the packet decoder.
All truth tables have bounded arity. All lane numbers are relative to one
copy, so neither the body nor the stored sidecar repeats with the bundle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports BottomRepeat Inherited
open scoped Classical
open private scalar_records_le from OAI.Computability.BorderVNP.CellPacketInputSize
open private small_list factor_fields from OAI.Computability.BorderVNP.CellPacketFields

/-- Public bit reservation for one box whose factor count and relative stride
are both at most the indicated capacity. -/
def bodyBudget (capacity : ℕ) : ℕ := (1+19*capacity)*(2*(max 8 capacity).size+2)

private theorem truth_words {ws : List ℕ} {rs : List Bool} (h : (Factor.truth ws rs).TableBound 8) :
    (Packet.factor (.truth ws rs)).length ≤ 19 := by
  obtain ⟨hw,hr⟩ := h
  simp [Packet.factor,Packet.vector]
  omega

private theorem body_words (fs : List Factor) (h : ∀ f ∈ fs,(Packet.factor f).length ≤ 19) :
    (Packet.fieldList Packet.factor fs).length ≤ 1+19*fs.length := by
  have hh : (fs.flatMap Packet.factor).length ≤ 19*fs.length := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      have hf := h f List.mem_cons_self
      have ht := ih fun a ha => h a (.tail _ ha)
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
      omega
  simp only [Packet.fieldList,List.length_cons]
  omega

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
local notation "rows₀" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "sz" => bottomStride (capFine+incoming G v) capReport
local notation "box" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID
  groupID v rules capFine capReport
local notation "sites" => Fintype.card {u : N.Site // cell u = v}


/-- Bound every actual key, table length, and scalar of the immutable one-copy
directory. The formerly weighted source tag is serialized in the sidecar. -/
theorem stored_factorFields (hf : GridBoxes.stride N cell v ≤ capFine) (hr : count rows₀ ≤ capReport)
    (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3)
    : ∀ f ∈ box, Packet.FactorFields f (max 8 sz) := by
  have within := stored_within N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules capFine capReport hf hr
  have tables := born_tableBound N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules 0 capFine capReport degree
  intro f hm
  obtain ⟨ws,rs,rfl⟩ := stored_truth N cell position pack width owner lane aligned siteID edgeID
    portID channelID groupID v rules capFine capReport f hm
  have ht : (Factor.truth ws rs).TableBound 8 := tables box List.mem_cons_self _ hm
  have reads : ∀ k ∈ ws, k < sz := within (.truth ws rs) hm
  refine ⟨⟨⟨ht.1.trans (le_max_left ..),ht.2.trans (le_max_left ..)⟩,?_⟩,trivial⟩
  exact fun k hk => (reads k hk).le.trans (le_max_right ..)

/-- The true framed private body fits any public reservation derived from the
fine-site capacity plus the private per-copy stride. -/
theorem stored_body_bits (hf : GridBoxes.stride N cell v ≤ capFine) (hr : count rows₀ ≤ capReport)
    (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3)
    (capacity : ℕ) (room : sites+sz ≤ capacity) :
    (Packet.Source.boxBody box).length ≤ bodyBudget capacity := by
  have hlen := (stored_length_le N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules capFine capReport hf).trans room
  have htbl := born_tableBound N cell position pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules 0 capFine capReport degree
  have hw := body_words box (fun f h => by
    obtain ⟨ws,rs,rfl⟩ := stored_truth N cell position pack width owner lane aligned siteID edgeID
      portID channelID groupID v rules capFine capReport f h
    exact truth_words (htbl box List.mem_cons_self _ h))
  have hfactors := stored_factorFields N cell position pack width owner lane aligned siteID edgeID
    portID channelID groupID v rules capFine capReport hf hr degree
  have fields := small_list (U := max 8 capacity) Packet.factor box (hlen.trans (le_max_right ..))
    (fun f hm i hi => by
      have hh := factor_fields f (hfactors f hm) i hi
      have hsz : sz ≤ capacity := (Nat.le_add_left _ _).trans room
      omega)
  apply (scalar_records_le (Packet.fieldList Packet.factor box) (L := (max 8 capacity).size)
    (fun i hi => Nat.size_le_size (by have h := fields i hi; omega))).trans
  exact Nat.mul_le_mul_right _ (hw.trans (by omega))

/-- The actual site string with one fixed-width three-field sidecar entry per
weighted original factor has the promised width, independently of copy count. -/
theorem stored_description_bits (hf : GridBoxes.stride N cell v ≤ capFine) (hr : count rows₀ ≤ capReport)
    (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3)
    (header capacity : ℕ) (room : sites+sz ≤ capacity) :
    header+(Packet.Source.boxBody box).length+
      (TallySidecar.bits header (positions (capFine+incoming G v) rows₀)).length ≤
      header+bodyBudget capacity+header*(1+3*capReport) :=
  TallySidecar.description_cap header (bodyBudget capacity) capReport _ _
    (stored_body_bits N cell position pack width owner lane aligned siteID edgeID portID channelID
      groupID v rules capFine capReport hf hr degree capacity room)
    (by simpa only [positions_length] using hr)

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
