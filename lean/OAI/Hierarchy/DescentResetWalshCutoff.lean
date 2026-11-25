import OAI.Hierarchy.DescentPackedWalshRead
import OAI.Hierarchy.DescentResetCutoffTable

namespace OAI
/-! # The selected reset cutoff reads the actual first Walsh column -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentGL DescentColonies DescentPlainTerminal.Suffix
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b w out : ℕ}

theorem zero_ordinal (l : ℕ) : (ordinal l (fun _=>false)).val=0 := by
  have zero (j : ℕ) : value j (fun _=>0)=0:=by
    induction j with
    | zero=>rfl
    | succ j ih=>change 2*value j (fun _=>0)+(0:ZMod 2).val=0;rw [ih];rfl
  exact zero l

def firstTotal (B : Bank) (p : Expr) (b : ℕ) := Expr.op .mask (.lookup B p) (.lit (2^b-1))

theorem firstTotal_read (B : Bank) (p : Expr) (mem : Memory w) (tick : Word w)
    (host : Fin H) (fit : B.Fits w out) (room : H*2^u≤B.size) (width : b≤w)
    (addr : p.eval mem tick=((row host (fun _ : Fin u=>false)).val:Word w))
    (x : Block (u+l)→ℕ) (measured : digit b (ordinal l (fun _=>false)).val
      (mem (B.base+(row host (fun _ : Fin u=>false)).val)).val=∑i : Bits (u+l),x (address (u+l) i)) :
    (firstTotal B p b).eval mem tick=((∑z,x z:ℕ):Word w) := by
  let i:=row host (fun _ : Fin u=>false)
  have sm:=i.isLt.trans_le room
  have mask : 2^b-1<2^w:=(Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide) width)
  rw [zero_ordinal,(address (u+l)).sum_comp] at measured
  simp only [digit,Nat.zero_add,Nat.mul_one,Nat.mul_zero,pow_zero,Nat.div_one] at measured
  simp only [firstTotal,Expr.eval,addr,RowOp.opcode,BinaryOp.eval,
    Fin.val_cast_of_lt mask,Nat.and_two_pow_sub_one_eq_mod]
  change Fin.ofNat (2^w) ((B.read mem (i.val:Word w)).val % 2^b) = _
  rw [DescentPackedZip.bank_read B mem sm fit]
  exact congrArg (fun k:ℕ=>(k:Word w)) measured

theorem cutoff_at (L : Bank) (index left right : Expr) (mem : Memory w) (tick : Word w)
    (target : Fin H) (limit : L.Fits w out) (rows : H*2^u≤L.size) (width : b≤w)
    (addr : index.eval mem tick=((row target (fun _ : Fin u=>false)).val:Word w))
    (flow : Block (u+l)→ℕ) (measured : digit b (ordinal l (fun _=>false)).val
      (mem (L.base+(row target (fun _ : Fin u=>false)).val)).val=∑i : Bits (u+l),flow (address (u+l) i))
    (base levels total K scale bound j z : ℕ) (src : left.eval mem tick=(j:Word w))
    (dst : right.eval mem tick=(z:Word w)) (depthFit : max j z<2^levels) (sumFit : (∑x,flow x)<2^total)
    (word : levels+total≤w) (rom : Cutoff.Resident base levels total K scale bound mem) :
    (Cutoff.term base levels total left right (firstTotal L index b)).eval mem tick=
      (threshold K scale (max j z) (∑x,flow x) bound:ℕ) :=
  Cutoff.read base levels total K scale bound left right (firstTotal L index b) mem tick j z _ src dst
    (firstTotal_read L index mem tick target limit rows width addr flow measured) depthFit sumFit word rom

end
end Hierarchy.DescentPackedWalsh

end OAI
