import OAI.Hierarchy.DescentDatedLocalScale
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.SmallAt
open DescentCompiler.TerminalScale Filter
variable {ι : ℕ→Type*} {J : ℕ→ℕ} {a : ∀h,ι h→ℕ}

/-- Local field counts fit the universal address exponent even before buying the
stronger half-word estimates used by the actually installed tables. -/
theorem bounded (room : SmallAt J a) (height : ∀ᶠ h:ℕ in atTop,J h≤h) : Bounded a :=by
  obtain ⟨A,short⟩:=room
  refine ⟨2*A,?_⟩
  filter_upwards [height,short,eventually_ge_atTop 1] with h large cap pos
  intro i
  apply (cap i).trans
  unfold scale
  apply Nat.pow_le_pow_right (by decide)
  have add:=Nat.mul_le_mul_left A (show J h+1≤2*h by omega)
  simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using add

theorem log_bounded (B : ℕ) (r : SmallAt (fun h=>Nat.log 2 h/(2*B)) a) : Bounded a :=
  r.bounded (Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h))
end Hierarchy.DescentDatedAddressBook.SmallAt

end OAI
