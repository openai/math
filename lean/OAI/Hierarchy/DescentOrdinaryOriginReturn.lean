import Mathlib.Util.AssertNoSorry
import OAI.Hierarchy.DescentOrdinaryOriginMask
import OAI.Hierarchy.DescentOrdinaryOriginPrice

namespace OAI
/-! # Return each real ordinary W compactor donor to the next physical checkpoint -/

namespace Hierarchy.DescentOrdinaryOriginMask
open DescentOrdinaryOriginReshape DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentPacking.PackedMatch.Local DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentHaloWalkRAM DescentPackedActorMask DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- The final low, host, group and block counts are the original rectangular
coordinates published by W. One cell contains every one-based donor ordinal
for the local compacted node list. -/
structure Return where
  degree : ℕ
  depth : ℕ
  oldNodes : ℕ
  capacity : ℕ
  newNodes : ℕ
  ordinalBits : ℕ
  hosts : ℕ
  lows : ℕ
  groups : ℕ
  blocks : ℕ
  lanes : ℕ

namespace Return
variable (R : Return)
local notation "D" => R.degree
local notation "k" => R.depth
local notation "K" => R.oldNodes
local notation "K₁" => R.newNodes
local notation "b" => R.ordinalBits
local notation "H" => R.hosts
local notation "J" => R.groups
local notation "Q" => R.lows
local notation "r" => R.blocks
local notation "M" => R.lanes
local notation "N" => nodes (breadth D*2^k) K R.capacity
def grid : DescentOrdinaryOriginReshape.Layout :=⟨H,Q,J,r,b*K₁,M⟩
def law := DescentOrdinaryOriginMask.law (nodes (breadth D*2^k) K R.capacity) K₁ b
def rowsAt (base : ℕ) := DescentOperandFamilyBook.endAddress 1 1 (1*N) (M*r) base
def finish (base : ℕ) := R.grid.finish (R.rowsAt base)
def preparationWords := R.finish 0
def returned (base : ℕ) (i : Fin r) :=R.grid.returned (R.rowsAt base) i
variable (C : Fin R.lows → DescentOrdinaryAtomFieldRAM.ScalarOperand.Refs
  R.degree R.depth R.oldNodes R.capacity)
def expr (base : ℕ) (i : Fin R.lows) : Expr :=
  DescentOperandFamilyBook.expr R.law (R.lanes*R.blocks) base (0 : Fin 1)
    (fun _ : Fin 1=>DescentOrdinaryOriginMask.mask (C i))
def program (w base : ℕ) :=
  (DescentOperandFamilyBook.program R.law (M*r) base w).seq (R.grid.program w (R.rowsAt base) (R.expr C base))
def image {w} (base : ℕ) (m : Memory w) :=
  R.grid.image (R.rowsAt base) (R.expr C base) (DescentOperandFamilyBook.image R.law (M*r) base m)
def ticks (base : ℕ) := DescentOperandFamilyBook.ticks 1 1 (1*N) (M*r)+R.grid.ticks (R.rowsAt base) (R.expr C base)

def phase (base w : ℕ) : NativePhase w :=
  ⟨R.program C w base,R.ticks C base,R.image C base,cheap_seq
    (@DescentStaticWordColumn.cheap w base _ _) (R.grid.cheap w _ _)⟩

theorem affine (base : ℕ) : R.finish base=base+R.preparationWords :=by
  simp only [finish,preparationWords,R.grid.affine,rowsAt,DescentOperandFamilyBook.endAddress,Nat.zero_add,Nat.add_assoc]

theorem table_before {w} (base : ℕ) (space : R.finish base<2^w) : R.rowsAt base<2^w:=by
  obtain ⟨one,two,three⟩:=R.grid.allocation (R.rowsAt base)
  change R.grid.finish (R.rowsAt base)<2^w at space
  omega

theorem framed {w} (base : ℕ) (m : Memory w) (fits : ∀i,(mask (C i)).Fits w base)
    (space : R.finish base<2^w) :
    (R.program C w base).Exec m (R.image C base m) (R.ticks C base) ∧ CheapCode (R.program C w base) ∧
      ∀i,i<base ∨ R.finish base≤ i→R.image C base m i=m i :=by
  let h:=R.table_before base space
  obtain ⟨mount,cheap,save,_⟩:=DescentOperandFamilyBook.any R.law (M*r) base m h
  have access i : (R.expr C base i).Fits w (R.rowsAt base):=
    DescentOperandFamilyBook.expr_fits R.law (M*r) base 0 _ (fun _=>fits i) h
  obtain ⟨run,keep⟩:=R.grid.framed (R.rowsAt base) (R.expr C base) _ access space
  refine ⟨?_,cheap_seq cheap (R.grid.cheap _ _ _),?_⟩
  · intro P S A mach pc reg pub stop rom advice cfg raw enter same
    exact Procedure.Exec.then mount run mach pc reg pub stop rom advice cfg raw enter same
  intro i away
  have lower:base≤R.rowsAt base:=Nat.le_add_right ..
  have lim:R.rowsAt base≤R.finish base:=by
    obtain ⟨one,two,three⟩:=R.grid.allocation (R.rowsAt base)
    change _≤R.grid.finish _
    omega
  rcases away with lt|gt
  · exact (keep i (.inl (lt.trans_le lower))).trans (save i (.inl lt))
  · exact (keep i (.inr gt)).trans (save i (.inr (lim.trans gt)))

theorem stepped {w} (base : ℕ) (m : Memory w) (fits : ∀i,(mask (C i)).Fits w base)
    (space : R.finish base<2^w) : (R.phase C base w).Runs m :=
  (R.framed C base m fits space).1

theorem originReturned {w a nb mb} (base : ℕ) (m : Memory w) (hm : 0<M) (hr : 0<r)
    (V : Fin Q→Values D k K R.capacity H (J*r) a nb mb)
    (measured : ∀i,Measured (C i) (V i) K₁ (M*r) base m) (space : R.finish base<2^w) :
    ∀i : Fin r,Reads (R.returned base i)
      (DescentScalarBookReshape.book (fun l h g=>selection N K₁ b (marked (V l) h g)) i) M (R.image C base m) :=by
  have got i:=issued (C i) (V i) K₁ b (M*r) base m (measured i) (R.table_before base space)
  exact R.grid.originReturned (R.rowsAt base) (R.expr C base) _ (fun i=>(got i).1) space
    hm hr _ (fun i=>(got i).2)


end Return
end
end Hierarchy.DescentOrdinaryOriginMask

end OAI
