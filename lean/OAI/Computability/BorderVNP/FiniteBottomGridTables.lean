import OAI.Computability.BorderVNP.PackedBottomScalarWiring
import OAI.Computability.BorderVNP.PackedBankInheritedValue

/-! # Reindexing an actual finite grid cell's supplied inputs

The compact supplied word reads each crossing cable at its packed lane and
each exterior bit at the slot owned by its group. Summing the private fine
guesses at these inputs evaluates the original cell contraction with the
physical channel padding test.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing CellAddresses Inherited BottomGridBank
open scoped Classical BigOperators

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable {F : Type*} [CommSemiring F]

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "grid" => Network.uniformGrid (Network.cellNetwork N cell position) src dst H
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "pad" => publicPad N cell position pack width owner channelID groupID v

/-- One copy of the packed, grouped physical table is exactly the sum of the
private original-wire choices when all its public cable padding tests pass. -/
theorem oneCopy_entry (T : N.Tables F)
    (z : ∀ e : Incident G v, Fin ((G).width e.val) → Bool)
    (x : ∀ p : Attached G v, Fin (width p.val) → Bool) :
    (if pad (inputWords G channelID groupID v z x) then
      ∑ g, factor N cell v edgeID portID T g (fun k => inputWords G channelID groupID v z x (fineIndex k))
     else 0) =
      (grid).externalTables width lane owner aligned (pack.tables (N.cellTables cell position T)) v z x := by
  let w (e : Boundary N cell v) (k : Fin (N.width e.val.val)) := z
    ⟨pack.channel e.val,e.property.imp ((pack.src_eq e.val).trans) ((pack.dst_eq e.val).trans)⟩
    (pack.address ⟨e.val,k⟩).2
  let args (p : {p : P // cell (N.attach p) = v}) (_ : Fin 1) :=
    x ⟨(lane p.val).1,(aligned p.val).trans p.property⟩ (lane p.val).2
  let values : ∀ u : Supplied N cell v, Fin (suppliedWidth N cell v u) → Bool := fun u =>
    match u with | .inl e => w e | .inr p => args p
  have pull : (fun k => inputWords G channelID groupID v z x (fineIndex k)) =
      (suppliedWords N cell v edgeID portID).symm values := by
    apply (suppliedWords N cell v edgeID portID).injective
    rw [Equiv.apply_symm_apply]
    funext u k
    change inputWords G channelID groupID v z x (fineIndex (suppliedOrdinal N cell v edgeID portID u k)) = _
    rw [publicIndex_supplied]
    cases u with
    | inl e => exact inputWords_wire G channelID groupID v z x _ _
    | inr p => exact inputWords_port G channelID groupID v z x _ _
  have guard : pad (inputWords G channelID groupID v z x) ↔
      ∀ q : {q : Q // src q = v ∨ dst q = v}, pack.ZeroPad q.val (z q) := by
    simp only [publicPad,inputWords_wire]
  rw [pull,Network.externalTables,Network.ChannelPacking.tables,propext guard]
  split
  · convert! sum_factor N cell v edgeID portID position T w args using 2
    congr 2
    funext u
    cases u <;> rfl
  · rfl

omit [Fintype P] [Fintype A] in
/-- Grouping the physical repeated external port words commutes with reading
each copy's own channel and external subwords in the original grouped grid. -/
theorem repeated_entry (copies : ℕ) (T : N.Tables F)
    (z : Incident (BottomRepeat.wide G copies) v → Fin (copies*H) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G copies) v, Fin (copies*width p.val) → Bool) :
    (∏ i : Fin copies, (grid).externalTables width lane owner aligned (pack.tables (N.cellTables cell position T))
      v (fun e k => z e (finProdFinEquiv (i,k))) (fun p k => x p (finProdFinEquiv (i,k)))) =
    ((grid).repeatGrid copies).externalTables _ (Network.repeatLane width lane copies) owner
      (fun p => aligned p.2) ((grid).repeatTables copies (pack.tables (N.cellTables cell position T))) v z x := rfl

end Packing.FiniteBottom

end BorderVNP
end Computability
end OAI
