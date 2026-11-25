import OAI.Hierarchy.DescentTerminalPointerColumns
import OAI.Hierarchy.DescentTerminalPointerFrame

namespace OAI
/-! # Host and literal costs of the reached terminal argument family -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup DescentTerminalPointerFrame DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr

theorem column_bound {T cap N A s : ℕ} (pos : 0 < T) (c : cap≤(2*T)^s) (n : N≤(2*T)^s) (a : A≤(2*T)^s) :
    columns cap N A≤(2*T)^(2*s+4) := by
  let u:=(2*T)^s
  have one : 1≤u:=Nat.one_le_pow _ _ (by omega)
  have square : u≤u*u:=Nat.le_mul_of_pos_right u one
  have na:N*A≤u*u:=Nat.mul_le_mul n a
  have scale : 16≤(2*T)^4:=Nat.pow_le_pow_left (by omega : 2≤2*T) 4
  calc
    columns cap N A ≤ 16*(u*u) := by dsimp [columns];change cap≤u at c;change N≤u at n;omega
    _ ≤ (2*T)^4*(u*u) := Nat.mul_le_mul_right _ scale
    _ = (2*T)^(2*s+4) := by
      dsimp only [u]
      rw [show 2*s = s+s by omega, pow_add, pow_add]
      ring

theorem tariff {L d h : ℕ} (width : d*L≤h/2) (slot : d≤h/2) :
    DescentTerminalPointerFrame.size L d≤(L+1)*2^(h/2) := by
  have m:=Nat.pow_le_pow_right (by decide : 0 < 2) width
  have n:=Nat.pow_le_pow_right (by decide : 0 < 2) slot
  unfold DescentTerminalPointerFrame.size
  rw [Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ n) m

/-- Runtime and literal costs for one old block, including the complete table mount. -/
theorem clock_split (L d h shops : ℕ) (width : d*L≤h/2) (slot : d≤h/2) :
    (4+10*DescentTerminalPointerFrame.size L d)+(4+shops*(16+26*L)) ≤
      8+10*((L+1)*2^(h/2))+shops*(16+26*L) := by
  have bound:=tariff width slot
  omega

theorem shared_hardware {L d b : ℕ} (src : Fin L→ Bank) (f : (Fin L→ Cell d)→ Cell b) (w base n : ℕ) :
    names (DescentTerminalPointerFrame.program w base src n f)=
      15*(DescentTerminalPointerFrame.size L d+1)+(35+52*L) := by
  simp only [DescentTerminalPointerFrame.program,DescentTerminalPointerFrame.mount,names_seq,names_mount,names_scan,
    DescentTerminalPointerFrame.row_work]
  omega

end Hierarchy.DescentTerminalPointerDigits

end OAI
