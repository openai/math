import OAI.Hierarchy.DescentResetPriorHostPad
import OAI.Hierarchy.DescentOrdinaryHostPadPrice
import OAI.Hierarchy.DescentRetainedMovementBits
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The full CPU and address bill for the predecessor host alignment -/
namespace Hierarchy.DescentResetPriorHostPad.Shape
open DescentOrdinaryHostPad DescentSIMDLookup DescentSixParty.Chronology DescentDatedAddressBook
open DescentResetRetainedSetup DescentStaticWordColumn
open ProtocolRAM
noncomputable section
variable (s : Shape)

theorem fee (base w : ℕ) (src : Fin s.dataRect.pages→Bank) (role : Fin s.blocks→Bank) :
    (s.phase base src role w).ticks+7*names (s.phase base src role w).program≤
      512*(s.dataRect.pages+1)*(s.dataRect.rows+1)+512*(s.roleRect.pages+1)*(s.roleRect.rows+1):=by
  have a:=s.dataRect.fee base src w
  have b:=s.roleRect.fee (s.roleStart base) role w
  simp only [phase,NativePhase.seq,names_seq]
  omega

def volume (h args role : ℕ) :=
  512*(s.dataRect.pages+1)*((s.newHosts+1)*h+s.newHosts*s.groups*args)+
  512*(s.blocks+1)*((s.newHosts+1)*h+s.newHosts*s.groups*role)

theorem word_bill (base w h ratio args token : ℕ) (src : Fin s.dataRect.pages→Bank) (role : Fin s.blocks→Bank)
    (aPos : 0<s.operandLanes) (rPos : 0<s.roleLanes)
    (argFill : s.groups≤ s.operandLanes ∨ h≤ s.operandLanes*args)
    (roleFill : s.groups≤ s.roleLanes ∨ h≤ s.roleLanes*token) (word : w≤ratio*h) :
    ((s.phase base src role w).ticks+7*names (s.phase base src role w).program)*w≤ratio*s.volume h args token:=by
  have arg:=Layout.bounded_pitch_rows (H:=s.newHosts) aPos argFill
  have role_:=Layout.bounded_pitch_rows (H:=s.newHosts) rPos roleFill
  have at_ : (s.dataRect.rows+1)*h≤(s.newHosts+1)*h+s.newHosts*s.groups*args:=by
    change (Overlap.rows s.newHosts s.groups s.operandLanes+1)*h≤_
    rw [Nat.add_mul,Nat.one_mul,Nat.add_mul,Nat.one_mul];omega
  have rt : (s.roleRect.rows+1)*h≤(s.newHosts+1)*h+s.newHosts*s.groups*token:=by
    change (Overlap.rows s.newHosts s.groups s.roleLanes+1)*h≤_
    rw [Nat.add_mul,Nat.one_mul,Nat.add_mul,Nat.one_mul];omega
  calc
    _ ≤ (512*(s.dataRect.pages+1)*(s.dataRect.rows+1)+512*(s.roleRect.pages+1)*(s.roleRect.rows+1))*(ratio*h):=
      Nat.mul_le_mul (s.fee base w src role) word
    _ = ratio*(512*(s.dataRect.pages+1)*((s.dataRect.rows+1)*h)+512*(s.blocks+1)*((s.roleRect.rows+1)*h)):=by
      change _=ratio*(512*(s.dataRect.pages+1)*((s.dataRect.rows+1)*h)+512*(s.roleRect.pages+1)*((s.roleRect.rows+1)*h))
      ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ at_) (Nat.mul_le_mul_left _ rt))

variable {ι : ℕ→Type*}
structure ScalarRoom (s : ∀h,ι h→Shape) : Prop where
  hosts : Bounded (fun h i=>(s h i).newHosts)
  groups : Bounded (fun h i=>(s h i).groups)
  args : Bounded (fun h i=>(s h i).arguments)
  blocks : Bounded (fun h i=>(s h i).blocks)
  dataPitch : Bounded (fun h i=>(s h i).operandLanes)
  rolePitch : Bounded (fun h i=>(s h i).roleLanes)

theorem extent_rate (s : ∀h,ι h→Shape) (r : ScalarRoom s) : Bounded (fun h i=>(s h i).endAddress 0):=by
  have part {M : ∀h,ι h→ℕ} (pitch : Bounded M) : Bounded (fun h i=>chunks (s h i).groups (M h i)):=
    (r.groups.add pitch).of_le (fun h i=>(Nat.div_le_self _ _).trans (Nat.sub_le ..))
  have dataRows:=r.hosts.mul (part r.dataPitch)
  have roleRows:=r.hosts.mul (part r.rolePitch)
  have pages:=((Bounded.const 2).add ((Bounded.const 7).mul r.args)).mul r.blocks
  have d:=((pages.add (Bounded.const 1)).mul dataRows).add ((dataRows.add (Bounded.const 1)).padded)
  have z:=((r.blocks.add (Bounded.const 1)).mul roleRows).add ((roleRows.add (Bounded.const 1)).padded)
  exact (d.add z).of_le (fun h i=>by
    simp only [endAddress,roleStart,dataRect,roleRect,Rect.finish,Rect.total,Rect.rows,Nat.zero_add,Nat.add_assoc]
    rfl)

end
end Hierarchy.DescentResetPriorHostPad.Shape

end OAI
