import OAI.Computability.BorderVNP.PackedTableBoundGrid
import OAI.Computability.BorderVNP.PackedBottomBoxScalars
import OAI.Computability.BorderVNP.CellPacketFieldMonotone

/-! # Relative fields and global IDs of actual routed bottom-grid private boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse

/-- All private key addresses and sizes are local; global identifiers of paid
gadget rows use their separate binary bound. -/
def Site.SplitFields (s : Site) (V U : ℕ) : Prop :=
  ∀ fs ∈ s.boxes, ∀ f ∈ fs, f.FieldBound V ∧ f.IDBound U

/-- Retaining earlier stages transports their complete relative fields and global IDs. -/
theorem Site.SplitFields.retain {s : Site} {V U : ℕ} (h : s.SplitFields V U) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).SplitFields V U := h

end Packing.Inherited

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

private def unstaged (V U : ℕ) (f : Factor) : Prop :=
  match f with
  | .unary wire _ => wire ≤ V
  | f => f.FieldBound V ∧ f.IDBound U

private theorem compareFields {a b V U : ℕ} (four : 4 ≤ V) (ha : a ≤ V) (hb : b ≤ V) :
    (compareUse a b).FieldBound V ∧ (compareUse a b).IDBound U := by
  simp [compareUse,Factor.IDBound,Factor.FieldBound,Factor.TableBound,ha,hb]
  omega

private theorem zeroFields {a V U : ℕ} (two : 2 ≤ V) (ha : a ≤ V) :
    (GridPadding.zeroFactor a).FieldBound V ∧ (GridPadding.zeroFactor a).IDBound U := by
  simp [GridPadding.zeroFactor,Factor.IDBound,Factor.FieldBound,Factor.TableBound,ha]
  omega

private theorem stageFields (rows : List Factor) (next V U : ℕ) (four : 4 ≤ V)
    (room : next+count rows ≤ V) (fields : ∀ f ∈ rows, unstaged V U f) :
    ∀ f ∈ stage next rows, f.FieldBound V ∧ f.IDBound U := by
  induction rows generalizing next with
  | nil => simp [stage]
  | cons f fs ih =>
    obtain ⟨hf,ht⟩ := List.forall_mem_cons.mp fields
    cases f with
    | unary wire report =>
      change next+(count fs+1) ≤ V at room
      simp only [stage,List.forall_mem_cons]
      exact ⟨compareFields four hf (by omega),ih _ (by omega) ht⟩
    | truth | sign | gadget =>
      simp only [stage,List.forall_mem_cons]
      exact ⟨hf,ih _ room ht⟩

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules

/-- Only the true one-copy slab and its optional staged use bits enter the numeric
private bound, even for a zero copy count. A source unary's original reported
address is replaced by a local two-input equality. Bottom cells have no gadget IDs. -/
theorem born_splitFields (copies capFine capReport V U : ℕ) (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3)
    (eight : 8 ≤ V) (fine : GridBoxes.stride N cell v ≤ capFine)
    (report : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (extent : capFine+incoming G v+capReport ≤ V) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).SplitFields V U := by
  change ∀ boxes ∈ [stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport],
    ∀ f ∈ boxes, Factor.FieldBound f V ∧ Factor.IDBound f U
  rw [List.forall_mem_singleton]
  simp only [stored,wiring,List.forall_mem_append]
  have countCap : count fs ≤ capReport := (count_le_length fs).trans (by
    simpa only [GridBoxes.factors,List.length_map,GridBoxes.siteList_length] using report)
  refine ⟨⟨stageFields _ _ _ _ (by omega) (by omega) ?_,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩
  · intro f hf
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hf
    cases hr : rules u with
    | unary wire port =>
      change (GridBoxes.lane N cell v edgeID portID u wire).val ≤ V
      exact (GridBoxes.lane N cell v edgeID portID u wire).isLt.le.trans (by omega)
    | truth tab =>
      have pass := GridBoxes.rule_factorFields N cell v edgeID portID u (Fintype.equivFin _) (degree u.val)
        eight (show GridBoxes.stride N cell v ≤ V by omega) (.truth tab) trivial
      exact Packet.factorFields_iff _ _ |>.mp pass
  · intro f hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    apply compareFields (by omega)
    · have hj := j.isLt; unfold GridBoxes.stride at fine; omega
    · have hj := (publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v j).isLt
      omega
  · intro f hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    have := List.mem_range.mp hj
    exact zeroFields (by omega) (by omega)
  · intro f hf
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
    apply zeroFields (by omega)
    unfold channelAddress
    have h := (sourceOrder G channelID groupID v (.inl ⟨j.1,j.2⟩)).isLt
    omega
  · intro f hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    have := List.mem_range.mp hj
    exact zeroFields (by omega) (by omega)

/-- The public scalar words of the true routed bottom birth obey the verified
repeat-box bound at their actual copy count, one-copy stride and full site size. -/
theorem born_scalarBound (copies capFine capReport : ℕ) :
    let stride := bottomStride (capFine+incoming G v) capReport
    let s := born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport
    s.ScalarBound (max 2 (max copies (max stride s.size))) := by
  intro stride s
  exact BottomRepeat.bornWith_scalarBound G channelID groupID v copies capFine stride
    (stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport)
    (Nat.le_add_right ..)

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
