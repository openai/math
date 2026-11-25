import OAI.Hierarchy.DescentSeedHeaderCharge
import OAI.Hierarchy.DescentSeedTokenSourceLayout
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # Address range of the role source on the original ballot tape -/
namespace Hierarchy.DescentExteriorShelf.Root
open Catalyst DescentSeedRoot DescentPackedSeed DescentSIMDLookup
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s h : ℕ)
local notation "A" => DescentPackedSeed.Primitive.pieces h s
local notation "n" => rows X R s h
local notation "flag" => DescentWideSeedFlags.endInput X R s h
omit [Field F] in
theorem role_source_table (wide : 16*digitsNeeded s≤h) :
    publicWords X+DescentDyadicSpan.span (DescentPackedSeed.Primitive.Source.jobs X R s h)≤
      (DescentWideSeedFlags.dictionary X R s h).base :=by
  let source:=publicWords X
  let jobs:=DescentPackedSeed.Primitive.Source.jobs X R s h
  have active:0 < A:=(occupancy h (8*digitsNeeded s) (by unfold digitsNeeded;positivity) (by omega)).1
  have countEq : n=jobs :=by
    rw [DescentPackedSeed.rows,grouped_multiplicity wide]
    change Fintype.card (Old X)*chunks (R*8) (A*8)=Fintype.card (Old X)*chunks R A
    rw [chunks_group R A 8 active (by decide)]
  have table : source+DescentDyadicSpan.span jobs ≤ (DescentWideSeedFlags.dictionary X R s h).base :=by
    change publicWords X+2^Nat.clog 2 jobs ≤ (publicWords X+2^Nat.clog 2 n)+_
    rw [countEq]
    exact Nat.le_add_right ..
  exact table

omit [Field F] in
theorem role_source_extent (wide : 16*digitsNeeded s≤h) :
    publicWords X+DescentDyadicSpan.span (DescentPackedSeed.Primitive.Source.jobs X R s h)≤flag:=
  (role_source_table X R s h wide).trans (Nat.le_add_right ..)

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
