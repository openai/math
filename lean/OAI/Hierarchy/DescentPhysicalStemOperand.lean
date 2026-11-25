import OAI.Hierarchy.DescentPhysicalResetTrunkScene

namespace OAI
/-! # Reading a signed physical stem column at the final trunk date -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable (v : CandidateFront) (floor : ℕ)
local notation "n" => (v.newHosts*chunks v.peer.groups v.peer.lanes)

def stemBank (x j : ℕ) : Bank :=
  ⟨v.stemOutput floor+(x*v.signedQueries+j)*n,Nat.clog 2 n⟩

def stemOperand (x j : ℕ) : Expr := .lookup (v.stemBank floor x j) .row

theorem stem_operand_work (x j : ℕ) : (v.stemOperand floor x j).work=7:=rfl

private theorem padding_end : v.mixed floor+span n≤ v.trunkEnd floor :=by
  have grow : v.mixed floor≤
      DescentResetTrunkCompactRows.rowBase (DescentResetTrunkCompactGather.geometry (v.mixed floor) v.newHosts)
        v.newHosts v.peer.groups v.peer.lanes :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have rest : v.mixed floor+span n≤ v.gathered floor:=Nat.add_le_add_right grow _
  exact rest.trans (Nat.le_add_right ..)

private theorem ordinal_bound (x : Fin v.blocks) (j : Fin v.signedQueries) :
    x.val*v.signedQueries+j.val< v.blocks*v.signedQueries :=by
  calc
    _< x.val*v.signedQueries+v.signedQueries:=Nat.add_lt_add_left j.isLt _
    _=(x.val+1)*v.signedQueries:=(Nat.succ_mul ..).symm
    _≤ v.blocks*v.signedQueries:=Nat.mul_le_mul_right _ x.isLt

variable (s : v.Scene) {w : ℕ}
include s in
theorem stem_bank_fits (room : v.trunkEnd floor<2^w) (x : Fin v.blocks) (j : Fin v.signedQueries) :
    (v.stemBank floor x.val j.val).Fits w (v.trunkEnd floor) :=by
  have last:=(v.trunk_regions floor s).2.2
  have off:=Nat.mul_le_mul_right n (v.ordinal_bound x j).le
  have start :=(Nat.add_le_add_left off (v.stemOutput floor)).trans last.le
  have stop :=(Nat.add_le_add_right start (span n)).trans (v.padding_end floor)
  change 0 < span n ∧ span n<2^w ∧ _≤ v.trunkEnd floor
  exact ⟨span_pos _,(Nat.le_add_left (span n) _).trans_lt (stop.trans_lt room),stop⟩

include s in
theorem stem_operand_fits (room : v.trunkEnd floor<2^w) (x : Fin v.blocks) (j : Fin v.signedQueries) :
    (v.stemOperand floor x.val j.val).Fits w (v.trunkEnd floor) :=
  ⟨v.stem_bank_fits floor s room x j,trivial⟩

theorem stem_operand_actual (safe : v.SceneRoom floor s w) (initial : Memory w) (room : v.trunkEnd floor<2^w)
    {bits : ℕ} (x : Fin v.blocks) (j : Fin v.signedQueries) (value : Fin v.newHosts→Fin v.peer.groups→Cell bits)
    (issued : ∀p : Row v.newHosts v.peer.groups v.peer.lanes,
      (v.received floor s safe).image initial
        (v.stemOutput floor+(finProdFinEquiv (x,j)).val*n+(row v.newHosts v.peer.groups v.peer.lanes p).val)=
        ((data value p).val:Word w)) :
    Source (v.stemOperand floor x.val j.val) value v.peer.lanes ((v.trunkScene floor s safe).image initial) :=by
  apply source_column (v.stemBank floor x.val j.val) (v.trunkEnd floor) (v.stem_bank_fits floor s room x j) _ value (span_ge _)
  intro p
  have index : (finProdFinEquiv (x,j)).val=x.val*v.signedQueries+j.val:=by
    change j.val+v.signedQueries*x.val=x.val*v.signedQueries+j.val
    ac_rfl
  have before : (v.stemBank floor x.val j.val).base+(row v.newHosts v.peer.groups v.peer.lanes p).val< v.mixed floor :=by
    have addr:=(row v.newHosts v.peer.groups v.peer.lanes p).isLt
    have next:=Nat.mul_le_mul_right n (v.ordinal_bound x j)
    rw [Nat.succ_mul] at next
    have last:=(v.trunk_regions floor s).2.2
    change v.stemOutput floor+(x.val*v.signedQueries+j.val)*n+_ < v.mixed floor
    omega
  have read:=issued p
  rw [index] at read
  exact (v.trunkScene_before floor s safe initial room _ before).trans read

theorem stem_operand_at_indices {X Q G bits : ℕ} (hx : v.blocks=X) (hq : v.signedQueries=Q) (hg : v.peer.groups=G)
    (safe : v.SceneRoom floor s w) (initial : Memory w) (room : v.trunkEnd floor<2^w)
    (x : Fin X) (j : Fin Q) (value : Fin v.newHosts→Fin G→Cell bits)
    (issued : ∀p : Row v.newHosts G v.peer.lanes,(v.received floor s safe).image initial
        (v.stemOutput floor+(finProdFinEquiv (x,j)).val*(v.newHosts*chunks G v.peer.lanes)+(row v.newHosts G v.peer.lanes p).val)=
        ((data value p).val:Word w)) :
    (v.stemOperand floor x.val j.val).Fits w (v.trunkEnd floor) ∧ Source (v.stemOperand floor x.val j.val)
      value v.peer.lanes ((v.trunkScene floor s safe).image initial) :=by
  subst X
  subst Q
  subst G
  exact ⟨v.stem_operand_fits floor s room x j,v.stem_operand_actual floor s safe initial room x j value issued⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
