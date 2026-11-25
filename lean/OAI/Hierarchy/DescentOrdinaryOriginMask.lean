import OAI.Hierarchy.DescentScalarBookColumns
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # The original selected actor of each occupied ordinary receiver row -/
namespace Hierarchy.DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM DescentPackedActorMask
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D k K cap H G a nb mb M w : ℕ}
set_option quotPrecheck false
local notation "d₀" => breadth D*2^k
local notation "a₀" => actors d₀ cap
local notation "n₀" => nodes d₀ K cap

def mask (C : Refs D k K cap) : Expr :=
  C.tables.actors.read (C.tables.targets.read C.want C.addr) C.counts
def marked (V : Values D k K cap H G a nb mb) (h : Fin H) (g : Fin G) : Cell (1*n₀) :=
  occupied d₀ K cap mb (target nb a₀ (V.wanted h g) (encode nb a₀ (V.venues h g))) (encode mb d₀ (V.counts h g))

theorem read_mask (C : Refs D k K cap) (V : Values D k K cap H G a nb mb)
    {K' base : ℕ} {m : Memory w} (data_ : Measured C V K' M base m) :
    (mask C).Fits w base ∧ Source (mask C) (marked V) M m:=by
  have flags:=read_data C.tables.targets C.want C.addr base data_.targetFits
    (target nb a₀) (target_zero ..) m data_.targets _ _ data_.wants data_.venues
  have scoped_ : (mask C).Fits w base:=by
    exact ⟨data_.actorFits.apply,data_.actorFits.right,data_.actorFits.shift,data_.actorFits.left⟩
  exact ⟨scoped_,
    read_data C.tables.actors _ C.counts base data_.actorFits (occupied d₀ K cap mb)
      (occupied_zero ..) m data_.actors _ _ flags data_.counts⟩

def selected (N K' b : ℕ) (bits : Cell (1*N)) (n : Fin K') : Cell b :=
  DescentPackedLocalAtoms.field K' ((encode 1 N).symm bits) (fun j=>((j.val+1:ℕ):Cell b)) n

def selection (N K' b : ℕ) (bits : Cell (1*N)) : Cell (b*K') :=
  encode b K' (selected N K' b bits)

def law (N K' b : ℕ) (_ : Fin 1) (x : Fin 1→Cell (1*N)) : Cell (b*K') :=selection N K' b (x 0)

private theorem zero (b n : ℕ) : encode b n (fun _=>0)=0 :=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell b))).val=0
  simp []

theorem selected_none (N K' b : ℕ) (bits : Cell (1*N)) (n : Fin K')
    (empty_ : ¬∃j,((encode 1 N).symm bits) j≠0 ∧ DescentPackedLocalAtoms.earlier ((encode 1 N).symm bits) j=n.val) :
    selected N K' b bits n=0:=by simp only [selected,DescentPackedLocalAtoms.field,dite_eq_right empty_]

theorem dead (N K' b : ℕ) (j : Fin 1) : law N K' b j (fun _=>0)=0:=by
  change encode b K' _=0
  rw [←zero b K']
  congr 1
  funext n
  apply selected_none
  rw [(show (encode 1 N).symm 0=fun _=>0 from (encode 1 N).symm_apply_eq.mpr (zero 1 N).symm)]
  simp

/-- The ordinal is one based. It indexes a forward walk, an old block and
either an old node or a new donor slot and its party. -/
theorem stamp_at (N K' b : ℕ) (bits : Cell (1*N)) (n : Fin K') (j : Fin N)
    (kept : (encode 1 N).symm bits j≠0) (rank : DescentPackedLocalAtoms.earlier ((encode 1 N).symm bits) j=n.val)
    (fits : N<2^b) : (((encode b K').symm (selection N K' b bits)) n).val=j.val+1:=by
  rw [selection,Equiv.symm_apply_apply]
  change (DescentPackedLocalAtoms.field K' _ _ n).val = _
  rw [DescentPackedLocalAtoms.field_at _ _ _ kept _ rank]
  have small : j.val+1<2^b := (Nat.succ_le_of_lt j.isLt).trans_lt fits
  exact Fin.val_cast_of_lt small

theorem issued (C : Refs D k K cap) (V : Values D k K cap H G a nb mb) (K' b M base : ℕ) (m : Memory w)
    (original : Measured C V K' M base m) (space : DescentOperandFamilyBook.endAddress 1 1 (1*n₀) M base<2^w) :
    let f:=law n₀ K' b
    let src:=fun _:Fin 1=>mask C
    (DescentOperandFamilyBook.expr f M base 0 src).Fits w (DescentOperandFamilyBook.endAddress 1 1 (1*n₀) M base) ∧
      Source (DescentOperandFamilyBook.expr f M base 0 src) (fun h g=>selection n₀ K' b (marked V h g)) M
          (DescentOperandFamilyBook.image f M base m):=by
  obtain ⟨fits,live⟩:=read_mask C V original
  exact DescentOperandFamilyBook.issued _ (dead n₀ K' b) M base 0 _ m
    (fun h g (_:Fin 1)=>marked V h g) (fun _=>fits) (fun _=>live) space

end
end Hierarchy.DescentOrdinaryOriginMask

end OAI
