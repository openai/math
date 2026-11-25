import OAI.Hierarchy.DescentPhysicalResetLeft
import OAI.Hierarchy.DescentRecordedResetCalendar

namespace OAI
/-! # Branch-independent scalar parameters of the physical reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentWalshPrecision ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

/-- The original cap tape and stage input banks determine the whole measured prefix.
The same public stencil parameters also fix the regrouping required after the selected basis. -/
def fromCalendar (S : AtomSchedule) (k tail age radix p f degree payload e n t : ℕ)
    (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput) : PhysicalReset :=
  let c:=S.groupWidth k tail age
  let m:=c+k
  let K:=quota S.rounds
  let b:=S.localWalshBits p m f K
  let l:=laneBits m payload b
  let cap:=(calendar.take age).prod*256
  let grain:=S.epochPower^S.priceExponent*(S.grainAt radix p (age+1)*radix)
  let st : DescentPlainTerminal.Suffix.StencilBook:=
    ⟨S.hostSize age,c,m,degree,degree,m-l,2^e,b,n,t,Nat.clog 2 (m+2),m+S.censusBits p⟩
  {k:=k,c:=2*cap,previousToken:=fun x=>addr x.1.val x.2.val,previousRoster:=roster,
   ingress:=⟨⟨S.hostSize age,2^c,out.funded.oldLanes,2^(l-k),k,degree,cap,Nat.clog 2 (degree+1)⟩,
     out.funded.precision,b,S.firstWidth radix p,grain⟩,
   hosts:=S.hostSize age,ports:=degree,high:=m-l,low:=l,bits:=b,short:=Nat.clog 2 (degree+1),
   lanes:=2^(l-k),depthCut:=f,fullBudget:=grain*cap,classBound:=K,grain:=grain,
   positive:=by dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega,
   gain:=gainBits m f K (S.censusBits p),payload:=payload,field:=b*2^k,groups:=2^c,re:=l-k-e,e:=e,
   successor:={out with middle:={out.middle with stencil:=st}}}

variable (S : AtomSchedule) (k tail age radix p f degree payload e n t : ℕ)
  (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput)
local notation "a₀" => fromCalendar S k tail age radix p f degree payload e n t calendar addr roster out
local notation "c₀" => S.groupWidth k tail age
local notation "m₀" => c₀+k
local notation "K" => quota S.rounds
local notation "l₀" => laneBits m₀ payload (S.localWalshBits p m₀ f K)

theorem calendar_dim : (a₀).high+(a₀).low=m₀ :=
  Nat.sub_add_cancel (Nat.min_le_left _ _)

theorem calendar_shape (packing : e≤l₀-k) : (a₀).StencilShape := by
  have cap:l₀≤ m₀:=Nat.min_le_left _ _
  refine StencilShape.of_dyadic (a₀) rfl rfl (calendar_dim S k tail age radix p f degree payload e n t calendar addr roster out).symm rfl ?_ rfl rfl ?_
  · change _*2^((c₀+k)-c₀)=_*2^k
    rw [Nat.add_sub_cancel_left]
    rfl
  · change (l₀-k-e)+e≤c₀
    omega

theorem calendar_packing (whereLow : k≤l₀) (batch : e≤l₀-k) :
    2^(a₀).re*2^(a₀).e*2^((a₀).high+(a₀).low-c₀)=2^(a₀).low := by
  rw [calendar_dim]
  change 2^(l₀-k-e)*2^e*2^(c₀+k-c₀)=2^l₀
  rw [←pow_add,←pow_add]
  congr 1
  omega

/-- This unfolds to the history-independent code and clock stated by the original cap receipt. -/
theorem calendar_prime (floor : ℕ) (src count : Bank) (w : ℕ) :
    let E:=(a₀).estimator floor
    let grain:=S.epochPower^S.priceExponent*(S.grainAt radix p (age+1)*radix)
    let cap:=(calendar.take age).prod*256
    (a₀).prime floor src count (S.groupCount age) degree w =
      PackedFlow.Canvas.Setup.resetPrefix E (S.hostSize age) degree k (S.groupCount age) cap (2^(l₀-k))
        (Nat.clog 2 (degree+1)) floor f K grain w addr roster src count ∧
    (a₀).primeTicks floor (S.groupCount age) degree w =
      PackedFlow.Canvas.Setup.resetTicks E (S.hostSize age) degree k (S.groupCount age) cap (2^(l₀-k))
        (Nat.clog 2 (degree+1)) floor f K grain w addr roster := ⟨rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
