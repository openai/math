import OAI.Hierarchy.DescentTerminalVertexFields
import OAI.Hierarchy.DescentTerminalPointerFrame

namespace OAI
/-! # A literal scan supplies the widths of the live private terminal words -/
namespace Hierarchy.DescentTerminalIssuedWidths
open DescentSIMDLookup DescentTerminalVertexFields DescentTerminalChronologicalBooks
open ProtocolRAM ProtocolRAMGeneratedWrite Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def widthDigit (p : ℕ) : Cell (Nat.clog 2 (p+1)) :=
  ⟨p,(Nat.lt_succ_self p).trans_le (Nat.le_pow_clog (by decide : 1<2) (p+1))⟩

/-- Every group receives the same private widths. Family two selects the live slots. -/
def word (H groups p : ℕ) : Cell ((Nat.clog 2 (p+1)*H)*groups) :=
  encode _ groups (fun _=>encode _ H (fun _=>widthDigit p))

def literal (H groups p : ℕ) : Expr := .lit (word H groups p).val

theorem within_span (q t H N A p groups : ℕ) :
    (Nat.clog 2 (p+1)*H)*groups≤groups*span q t H N A p := by
  have small : H*Nat.clog 2 (p+1)≤ span q t H N A p := by rw [DescentTerminalVertexFields.size];omega
  calc
    (Nat.clog 2 (p+1)*H)*groups=groups*(H*Nat.clog 2 (p+1)):=by ring
    _≤_:=Nat.mul_le_mul_left groups small

def program (bw out blocks shops H groups p : ℕ) :=
  scan bw out (blocks*shops) (literal H groups p)

def final {bw : ℕ} (out blocks shops H groups p : ℕ) (m : Memory bw) :=
  ProtocolRAM.image out (blocks*shops) (literal H groups p) m

theorem issued {bw : ℕ} (out blocks shops H groups p : ℕ) (m : Memory bw) (room : out+blocks*shops<2^bw) :
    (program bw out blocks shops H groups p).Exec m (final out blocks shops H groups p m) (4+(blocks*shops)*6) ∧
    CheapCode (program bw out blocks shops H groups p) ∧
    (∀i:Fin (blocks*shops),final out blocks shops H groups p m (out+i.val)=((word H groups p).val:Word bw)) ∧
    ∀a,a<out ∨ out+blocks*shops≤a→final out blocks shops H groups p m a=m a := by
  refine ⟨scan_exec out _ (literal H groups p) m trivial room,@scan_cheap _ _ _ _,?_,?_⟩
  · intro i
    exact read_image out _ (literal H groups p) m i
  · exact frame_image out _ (literal H groups p) m

theorem issued_digit {bw : ℕ} (out blocks shops H groups p : ℕ) (m : Memory bw)
    (room : out+blocks*shops<2^bw) (fits : (Nat.clog 2 (p+1)*H)*groups≤bw)
    (i:Fin (blocks*shops)) (g:Fin groups) (j:Fin H) :
    digit (Nat.clog 2 (p+1)) j.val (digit (Nat.clog 2 (p+1)*H) g.val
      (final out blocks shops H groups p m (out+i.val)).val)=p :=by
  have emit:=(issued out blocks shops H groups p m room).2.2.1 i
  have small: (word H groups p).val<2^bw :=
    (word H groups p).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fits)
  rw [emit,Fin.val_cast_of_lt small]
  simp only [word,digit_encode,widthDigit]

end
end Hierarchy.DescentTerminalIssuedWidths

end OAI
