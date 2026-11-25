import OAI.Hierarchy.DescentOrdinaryOriginReturn

namespace OAI
/-! # One shared donor table and the dated cost of issuing the origin rows -/
namespace Hierarchy.DescentOrdinaryOriginMask.Return
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentHaloWalkRAM DescentPackedActorMask DescentStaticWordColumn DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (R : Return)
local notation "N" => nodes (breadth R.degree*2^R.depth) R.oldNodes R.capacity
local notation "b" => R.ordinalBits
local notation "K₁" => R.newNodes
local notation "M" => R.lanes
local notation "r" => R.blocks
local notation "Q" => R.lows
local notation "tableWords" => DescentOperandFamilyBook.words 1 1 (1*N) (M*r)

def peak := max (2*N) (b*K₁)

/-- The same bound suffices for the selection-law ROM and each block of the transpose. -/
theorem tables {h : ℕ} (fit : R.peak*(M*r)≤h/2) :
    tableWords≤4*2^(h/2) ∧ 2^(((b*K₁)*r)*M)≤2^(h/2) :=by
  have left:= (Nat.mul_le_mul_right (M*r) (Nat.le_max_left (2*N) (b*K₁))).trans fit
  have right: ((b*K₁)*r)*M≤h/2 :=by
    calc
      ((b*K₁)*r)*M=(b*K₁)*(M*r):=by ac_rfl
      _≤_ := (Nat.mul_le_mul_right (M*r) (Nat.le_max_right (2*N) (b*K₁))).trans fit
  constructor
  · have power := Nat.pow_le_pow_right (n:=2) (by decide) left
    change (1+1)*(2*2^(((1*N)*1+1*N)*(M*r)))≤_
    simp only [one_mul,mul_one,Nat.reduceAdd,show N+N=2*N by omega]
    omega
  · exact Nat.pow_le_pow_right (n:=2) (by decide) right

theorem funded_extent {h : ℕ} (base : ℕ) (fit : R.peak*(M*r)≤h/2) :
    R.finish base≤base+(4+3*r)*2^(h/2)+2*(Q*R.grid.rows)+(5*r+2)*R.grid.nextRows+8 :=by
  obtain ⟨lookup,strip⟩:=R.tables fit
  have bands:=R.grid.extent (R.rowsAt base)
  change _≤base+tableWords+2*(Q*R.grid.rows)+3*(r*2^(((b*K₁)*r)*M))+
    5*(r*R.grid.nextRows)+2*R.grid.nextRows+8 at bands
  have smaller:=Nat.mul_le_mul_left r strip
  change R.grid.finish (R.rowsAt base)≤_
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

variable (C : Fin R.lows → DescentOrdinaryAtomFieldRAM.ScalarOperand.Refs
  R.degree R.depth R.oldNodes R.capacity)

theorem expr_price (base : ℕ) (i : Fin Q)
    (sources : (C i).want.work+(C i).addr.work+(C i).counts.work≤26) :
    (R.expr C base i).work≤73 :=by
  have measured : (mask (C i)).work≤48:=by
    simp only [mask,DescentPackedZip.work]
    omega
  exact DescentOperandFamilyBook.expr_work R.law (M*r) base 0 _ 48 (fun _=>measured)

theorem origin_table_bill {h} (w base : ℕ)
    (sources : ∀i,(C i).want.work+(C i).addr.work+(C i).counts.work≤26)
    (fit : R.peak*(M*r)≤h/2) :
    R.ticks C base+7*names (R.program C w base)≤
      2600*(Q+1)+160*(Q*R.grid.rows)+300*(r*R.grid.nextRows)+115*((4+r)*2^(h/2)) :=by
  obtain ⟨lookup,strip⟩:=R.tables fit
  have gridFee:=R.grid.invoice w (R.rowsAt base) 73 (R.expr C base) (fun i=>R.expr_price C base i (sources i))
  have literal : names (DescentOperandFamilyBook.program R.law (M*r) base w)=15*(tableWords+1):=by
    unfold DescentOperandFamilyBook.program Book.install
    simp only [names_mount,DescentOperandFamilyBook.words]
  have smaller:=Nat.mul_le_mul_left r strip
  rw [ticks,program,names_seq,literal,DescentOperandFamilyBook.ticks]
  change _+7*_≤(4+Q*(4+R.grid.rows*(2*73+4)))+
    ((4+10*(r*2^(((b*K₁)*r)*M)+2*(r*R.grid.nextRows)))+(4+r*R.grid.nextRows*54))+
    7*((15+Q*(11+4*73))+(15*((r*2^(((b*K₁)*r)*M)+2*(r*R.grid.nextRows))+1)+111)) at gridFee
  simp only [Nat.reduceMul,Nat.reduceAdd,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at *
  have row_form : Q*(R.grid.rows*150)=150*(Q*R.grid.rows):=by ac_rfl
  rw [row_form] at gridFee
  omega

end
end Hierarchy.DescentOrdinaryOriginMask.Return

end OAI
