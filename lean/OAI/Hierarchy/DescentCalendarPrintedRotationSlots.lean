import OAI.Hierarchy.DescentExteriorRotationSlot
import OAI.Hierarchy.DescentPublicRotationROM

namespace OAI
/-! # The installed table and saved rotation for a scheduled ordinary or reset date -/
namespace Hierarchy.DescentExteriorMatrixUpdate.Calendar
open DescentCompiler DescentSixParty.Chronology DescentGL DescentExterior
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable (S : AtomSchedule) (k tail base : ℕ) (reset : ℕ→Bool)
local notation "dim" => S.groupWidth k tail 0+k
local notation "fence" => stop S k tail base

private theorem table_end (age : ℕ) (alive : age<S.length) :
    tableAt S k tail base age+pages dim (localBits S k tail reset age)≤fence :=by
  have count:=page_room S k tail reset age
  have limit:=Nat.mul_le_mul_right (stride S k tail) alive
  rw [Nat.succ_mul] at limit
  change base+age*stride S k tail+_≤base+S.length*stride S k tail
  omega

theorem ordinary_slot (rotation : ℕ→ℕ) {w : ℕ} (m : Memory w) (age : ℕ) (alive : age<S.length)
    (previous : ∀i<S.length,rotation i<base) (fits : stop S k tail base+S.length+2<2^w)
    (printed : (entry S k tail base reset age alive).Resident m)
    (tag : reset age=false) (rot : Layout k)
    (saved : m (rotation age)=((matrixCode rot).val:Word w)) :
    Reel.Slot (reel S k tail base reset rotation) age (stop S k tail base)
      (ordinaryMap S k tail age alive) rot m :=
  let layout : Reel.Room (reel S k tail base reset rotation) w (S.groupWidth k tail 0+k)
      S.length (stop S k tail base) (stop S k tail base+S.length+1) :=
    Calendar.room S k tail base reset rotation previous fits
  ⟨by change localBits S k tail reset age=k; simp [localBits,tag],
    layout.previous age alive,layout.fit age alive,
    (previous age alive).trans_le (show base ≤ stop S k tail base from Nat.le_add_right ..),
    by simpa [reel,localBits,tag] using table_end S k tail base reset age alive,
    saved,by simpa [reel,entry,tag] using printed⟩

theorem reset_slot (rotation : ℕ→ℕ) {w : ℕ} (m : Memory w) (age : ℕ) (alive : age<S.length)
    (previous : ∀i<S.length,rotation i<base) (fits : stop S k tail base+S.length+2<2^w)
    (printed : (entry S k tail base reset age alive).Resident m)
    (tag : reset age=true) (rot : Layout (S.groupWidth k tail age+k))
    (saved : m (rotation age)=((matrixCode rot).val:Word w)) :
    Reel.Slot (reel S k tail base reset rotation) age (stop S k tail base)
      (resetMap S k tail age alive) rot m :=
  let layout : Reel.Room (reel S k tail base reset rotation) w (S.groupWidth k tail 0+k)
      S.length (stop S k tail base) (stop S k tail base+S.length+1) :=
    Calendar.room S k tail base reset rotation previous fits
  ⟨by change localBits S k tail reset age=S.groupWidth k tail age+k; simp [localBits,tag],
    layout.previous age alive,layout.fit age alive,
    (previous age alive).trans_le (show base ≤ stop S k tail base from Nat.le_add_right ..),
    by simpa [reel,localBits,tag] using table_end S k tail base reset age alive,
    saved,by simpa [reel,entry,tag] using printed⟩

end
end Hierarchy.DescentExteriorMatrixUpdate.Calendar

end OAI
