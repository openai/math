import OAI.Computability.BorderVNP.FiniteBottomGridModel
import OAI.Computability.BorderVNP.PackedBottomBoxLocality

/-! # Physical locality and size of the original finite-field boxes

Each fine site is stored once in its immutable box. Its relative lanes fit
the allocated fine slab, its rows lie in the finite scalar alphabet, and its
copied observations depend only on its own site's bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing CellAddresses Inherited BottomGridBank
open scoped BigOperators Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable {F : Type*} [Field F] [Fintype F]

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner

omit [Fintype C] [Field F] in
/-- Every retained fine site contributes exactly one stored scalar factor,
independently of the number of copies in the public bundle. -/
theorem scalarFactors_length (T : N.Tables F) :
    (scalarFactors N cell v siteID edgeID portID T).length = Fintype.card {z : N.Site // cell z = v} := by
  simp [scalarFactors]

omit [Fintype C] [Field F] in
/-- A fine site of degree at most three stores at most three physical lane
addresses and eight genuine scalar codes, each inside the field alphabet. -/
theorem scalarFactor_size (T : N.Tables F) (z : {i : N.Site // cell i = v})
    (h : Fintype.card (FieldDirectory.Lane N z.val) ≤ 3) :
    (scalarAddresses N cell v edgeID portID z).length ≤ 3 ∧
      (FieldDirectory.rowIds N T z.val).length ≤ 8 ∧
      ∀ j ∈ FieldDirectory.rowIds N T z.val, j < Fintype.card F := by
  refine ⟨by simpa [scalarAddresses] using h,(FieldDirectory.literal_size N T z.val h).2,?_⟩
  intro j hj
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
  exact (Fintype.equivFin F (FieldDirectory.row N T z.val k.val)).isLt

omit [Fintype C] [Field F] in
/-- Each scalar gadget reads only an allocated lane of its own fine site. -/
theorem scalarFactors_within (T : N.Tables F) (stride : ℕ) (h : GridBoxes.stride N cell v ≤ stride) :
    ∀ f ∈ scalarFactors N cell v siteID edgeID portID T, BottomRepeat.FactorWithin stride f := by
  intro f hf
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hf
  intro k hk
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
  exact (GridBoxes.lane N cell v edgeID portID z ((Fintype.equivFin _).symm i)).isLt.trans_le h

omit [Field F] in
/-- The initial concrete finite-field site is local for every copy count and
every fine capacity fitting the original hidden and supplied wires. -/
theorem finiteBorn_local (T : N.Tables F) (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine) :
    (finiteBorn N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
      T copies capFine fit).Local := by
  apply BottomRepeat.bornWith_local
  · exact le_rfl
  · rw [List.forall_mem_append]
    exact ⟨scalarFactors_within N cell siteID edgeID portID v T _ (fit.trans (Nat.le_add_right _ _)),
      wiring_within N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine fit⟩

end Packing.FiniteBottom

end BorderVNP
end Computability
end OAI
