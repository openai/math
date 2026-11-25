import OAI.Computability.BorderVNP.DiagonalPreparedOwnedJoin
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands
import OAI.Computability.BorderVNP.DiagonalNativeOwnedCellInputs
import OAI.Computability.BorderVNP.PackedFinalReportTemplate
import OAI.Computability.BorderVNP.DiagonalJointSparseReadback

/-! # Read the physical owner's private-wire width before choosing its bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CellMacro.Generator BorderVNP.Cube TeamContraction CompactMachine CellDispatch
open CellPacket CellPacketGeometry.History.Native.Terminal CellPacketGeometry CellSparse
open Crossing Packing Packing.Inherited Packing.CellAddresses
open scoped Classical

variable {T n w axes box lanes sel symbols C : ℕ} {id : TableEntry axes box lanes sel symbols → ℕ}
    (S : Fin T → PositiveTeam id SparseExterior.driver n w) (p : ∀ u, (S u).Prefix)
    (owner : Fin C → Fin T) (base : Fin T → ℕ)
    (table : ∀ u, OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,base u,C⟩ (ownerWord owner))

include table in
/-- The physical native three-word table at the sole owner of a numbered
cell contains that owner's tag and covers the cell ordinal. -/
theorem dispatchOwner (c : Fin C) :
    let u := owner c
    let f := Frame.ofMemory (S u).pub ((S u).postMemory (p u))
    c.val<f.count ∧ readings ((S u).postMemory (p u)) (f.address c.val)=f.team := by
  intro u f
  rw [show f = ⟨u.val,base u,C⟩ from (table u).frame]
  refine ⟨c.isLt,?_⟩
  exact ((table u).atRow c.val c.isLt).trans (by simp [ownerWord,u])

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (state : Site.Programs N)

private theorem place_private {Key Slot : Type} (field : SiteWords.Directory Key Slot (C+1))
    (places : Fin (C+1) → Placed Slot) (shape : TypedBatch.SourceShape places field) (c : Fin C) :
    (placeAt places c.val).privateWires=field.privateWires c.castSucc := by
  have number : (⟨min c.val C,Nat.lt_succ_of_le (min_le_right ..)⟩ : Fin (C+1))=c.castSucc :=
    Fin.ext (Nat.min_eq_left c.isLt.le)
  exact (congrArg (fun i => (places i).privateWires) number).trans (shape.privateWires c.castSucc)

include table in
/-- At every owned ordinal of every attained tuple, the published private
word is exactly the number of private bank digits of its decoded network.
The geometry emitter supplies its physical row header. The supplement, report
digits and restored exterior can vary arbitrarily at that row. -/
theorem published_owner_width {Key Slot : Type}
    (directory : Fin T → SiteWords.Directory Key Slot (C+1))
    (places : Fin T → Fin (C+1) → Placed Slot)
    (shape : ∀ u, TypedBatch.SourceShape (places u) (directory u))
    (emitted : ∀ (u : Fin T) (c : Fin C), (directory u).privateWires c.castSucc =
      FinalCell.privateBits N (fun v => (cell v).val) (fun v => (state v).program) c.val)
    (published : ∀ u, let f := Frame.ofMemory (S u).pub ((S u).postMemory (p u))
      ∀ i < f.count, readings ((S u).postMemory (p u)) (f.address i)=f.team →
        (((S u).generated (p u)).cell i).privateWires=(placeAt (places u) i).privateWires)
    (c : Fin C) : (((S (owner c)).generated (p (owner c))).cell c.val).privateWires =
      externalBase N cell c (fun v => (state v).program.size) := by
  obtain ⟨inside,owns⟩ := dispatchOwner S p owner base table c
  have real := published (owner c) c.val inside owns
  obtain ⟨guesses,localSize,_⟩ := FinalReports.bank_sizes N cell (fun v => (state v).program) c
  refine real.trans ((place_private (directory (owner c)) (places (owner c)) (shape (owner c)) c).trans
    ((emitted (owner c) c).trans ?_))
  exact congrArg₂ Nat.add guesses localSize

section Returning
variable {R : ℕ} (S₁ : Fin (R+1) → PositiveTeam id SparseExterior.driver n w) (p₁ : ∀ u, (S₁ u).Prefix)
    (owner₁ : Fin C → Fin (R+1)) (base₁ : Fin (R+1) → ℕ)
    (table₁ : ∀ u, OwnerTable (S₁ u).pub ((S₁ u).postMemory (p₁ u)) ⟨u.val,base₁ u,C⟩ (ownerWord owner₁))

include table₁ in
/-- Read the width on an attained native prefix directly from the two
physical receipts. The sparse task launcher returns its typed row image.
The supported continuation identifies its owner₁ call with that same
logical source, still before independent private bank bits are chosen. -/
theorem submitted_owner_width {Key Slot : Type}
    (directory : Fin (R+1) → SiteWords.Directory Key Slot (C+1))
    (places : Fin (R+1) → Fin (C+1) → Placed Slot)
    (shape : ∀ u, TypedBatch.SourceShape (places u) (directory u))
    (emitted : ∀ (u : Fin (R+1)) (c : Fin C), (directory u).privateWires c.castSucc =
      FinalCell.privateBits N (fun v => (cell v).val) (fun v => (state v).program) c.val)
    (records : Fin (R+1) → ℕ → List Record) (ext : Fin (R+1) → ℕ → SparseExterior.Field)
    (source : (u : Fin (R+1)) → PinStart.SparseSource id (fun v => (S₁ v).start) (u := u) (p₁ u))
    (submitted : ∀ u, (source u).arguments.rows.cells =
      fun i => SparseExterior.logicalCell (placeAt (places u) i) (records u i) (ext u i))
    (seen : ∀ u, let f := Frame.ofMemory (S₁ u).pub ((S₁ u).postMemory (p₁ u))
      ∀ i < f.count, readings ((S₁ u).postMemory (p₁ u)) (f.address i)=f.team →
        ((S₁ u).generated (p₁ u)).cell i=(source u).logicalAt i)
    (c : Fin C) : (((S₁ (owner₁ c)).generated (p₁ (owner₁ c))).cell c.val).privateWires =
      externalBase N cell c (fun v => (state v).program.size) := by
  apply published_owner_width S₁ p₁ owner₁ base₁ table₁ N cell state directory places shape emitted _ c
  intro u f i hi mine
  have hit := congrArg CellInput.privateWires (seen u i hi mine)
  have printed := congrArg CellInput.privateWires (congrFun (submitted u) i)
  exact hit.trans printed

end Returning

end RoutingISA.Evaluator.PositiveTeam

end BorderVNP
end Computability
end OAI
