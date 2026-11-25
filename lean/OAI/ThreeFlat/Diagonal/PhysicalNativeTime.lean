import OAI.ThreeFlat.Diagonal.PhysicalNativeTicks
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAdmission
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAdmission
import OAI.ThreeFlat.Diagonal.PhysicalBlockTreeSize
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # The counted native compressor at the diagonal trace scale -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression CompressorPacking Native.ShrinkStage Native.ShrinkStage.Resident
open NavigationPass NavigationDirectory
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

namespace Block
variable (B : Block F)

/-- The exact counted-loop clock in `Archive.run_repeated` fits in a single chunk
at each sufficiently large diagonal age. The local clock is the actual unrolled
stage clock used by the row induction. -/
theorem counted_cursor_time {W u k rem low : ℕ} (K : ℕ) (cur : Word W) (csr : Cursor)
    (hu : 40≤u) (levels : B.levels+1≤u) (coef : B.nativeCoefficient K≤u)
    (split : (B.repeat (u^8)).charge+rem=k) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) :
    let rows := (B.prefix (.done _)).length
    let steps := Program.nativeTicks K cur (B.repeat (u^8)) csr rem k
    u^8*(7+(rows*(rows*steps)+1))+4≤2^(u^10-u^4) := by
  intro rows steps
  have hp : 0<u := by omega
  have rowCap : rows≤u := by
    change (B.repeat 1).length≤u
    rw [program_length,B.repeat_effects_length,Nat.mul_one]
    exact levels
  have kCap : k≤u^11 := by
    have small := Nat.pow_le_pow_right hp (by decide : 6≤10)
    have room := Nat.mul_le_mul_left (u^10) (by omega : 3≤u)
    rw [pow_succ];omega
  have basis : 1+k*2^k≤u^12*2^k := by
    calc
      _ ≤ (1+u^11)*2^k := by
        rw [Nat.add_mul,Nat.one_mul]
        exact Nat.add_le_add (Nat.two_pow_pos _) (Nat.mul_le_mul_right _ kCap)
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        rw [pow_succ u 11]
        have m := Nat.mul_le_mul_left (u^11) (by omega : 2≤u)
        have pos : 0<u^11 := Nat.pow_pos hp
        omega
  have head : steps≤u^8*u*(u^12*2^k) :=
    (B.native_cursor_time K (u^8) cur csr split).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ coef) basis)
  let v := u^31*2^k
  have body : u^8*(rows*(rows*steps))≤v := by
    calc
      _ ≤ u^8*(u*(u*(u^8*u*(u^12*2^k)))) := by gcongr
      _ = _ := by dsimp [v];ring
  have room : 16*u^8≤v := by
    calc
      _ ≤ u*u^8 := Nat.mul_le_mul_right _ (by omega)
      _ = u^9 := by ring
      _ ≤ u^31 := Nat.pow_le_pow_right hp (by decide)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  have pos : 0<u^8 := Nat.pow_pos hp
  have decomposition : u^8*(7+(rows*(rows*steps)+1))+4=u^8*(rows*(rows*steps))+8*u^8+4 := by ring
  rw [decomposition]
  exact (show u^8*(rows*(rows*steps))+8*u^8+4≤8*v by omega).trans
    (register_exponents (by omega : 16≤u) (by omega : 31≤u) half depth).1


end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
