import OAI.Hierarchy.DescentVenueTailWordTariff
import OAI.Hierarchy.DescentStageVenueAny

namespace OAI
/-! # Joint word charge of three differently packed predecessor quantities and the new venue -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentSIMDLookup ProtocolRAM DescentPacking.PackedMatch.Local.Stage.DateBill
noncomputable section
variable (d : Date)
local notation "H" => d.hosts
local notation "G" => d.groups
local notation "r" => 2^d.k

/-- Public scalar coefficients multiplying the host/slot rectangle and the shared half-word pages. -/
def wordCoefficients (ratio : ℕ) : ℕ×ℕ :=
  (4096*ratio*(r*(2*d.cap)+1+2*(r+1))+1024*ratio*(r+d.degree+1),
   3*(2048*ratio)+115*ratio*r)

theorem word_bill_rows (B : Sources) (base w h s p a n U ratio : ℕ)
    (sp : 0<d.signedLanes) (pp : 0<d.paidLanes) (ap : 0<d.aliveLanes) (np : 0<d.lanes)
    (su : s≤U) (pu : p≤U) (au : a≤U) (nu : n≤U) (bus : w≤ratio*h)
    (signed : H*chunks G d.signedLanes*h≤H*h+H*G*s) (paid : H*chunks G d.paidLanes*h≤H*h+H*G*p)
    (alive : H*chunks G d.aliveLanes*h≤H*h+H*G*a) (next : H*chunks G d.lanes*h≤H*h+H*G*n)
    (sc : d.signedLanes≤h) (pc : d.paidLanes≤h) (nc : d.lanes≤h/2)
    (sb : DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤h/2)
    (pb : d.paidBits*d.paidLanes≤h/2) (ab : d.aliveLanes≤h/2) :
    bitTariff (d.program B base w) (d.ticks B base) ≤
      (d.wordCoefficients ratio).1*(h+2*H*h+2*H*G*U)+
      (d.wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h := by
  have newBound : d.lanes≤h := nc.trans (Nat.div_le_self ..)
  have actorBound : d.aliveLanes≤h := ab.trans (Nat.div_le_self ..)
  let fill:=h+2*H*h+2*H*G*U
  let lookup:=2*(h+1)^2*2^(h/2)*h
  have slot (u : ℕ) (l : u≤U) : h+2*H*h+(H*G)*(u+n)≤fill := by
    calc
      _ ≤ h+2*H*h+(H*G)*(U+U) :=by gcongr
      _ = _ :=by unfold fill;ring
  have head := DescentVenueSlabs.word_bill_rows d.signedShape (d.signedPage B) base w h s n ratio sp np sc newBound signed next sb bus
  have pay := DescentVenueSlabs.word_bill_rows d.paidShape (fun i=>B.paid i.val) (d.firstEnd base) w h p n ratio pp np pc newBound paid next pb bus
  have actors := DescentVenueSlabs.word_bill_rows d.aliveShape (fun i=>B.alive i.val) (d.secondEnd base) w h a n ratio ap np actorBound newBound alive next
    (by change 1*d.aliveLanes≤h/2;simpa using ab) bus
  have end_ := StageVenueTail.word_bill_rows (d.transported B base) (d.thirdEnd base) d.k H G d.lanes h n d.degree w ratio nc next bus
  have finalRect : h+2*H*h+H*G*n≤fill := by
    change h+2*H*h+H*G*n≤h+2*H*h+2*H*G*U
    gcongr
    omega
  have literal : 2^(h/2)*h≤lookup :=by
    have first : 1≤2*(h+1)^2 := Nat.succ_le_of_lt (by positivity)
    calc
      _ = 1*(2^(h/2)*h) :=by simp
      _ ≤ (2*(h+1)^2)*(2^(h/2)*h) :=Nat.mul_le_mul_right _ first
      _ = _ :=by unfold lookup;ring
  unfold Date.program Date.ticks
  repeat rw [bitTariff_seq]
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add head pay) actors) end_).trans ?_
  change 4096*ratio*(r*(2*d.cap)+1)*(h+2*H*h+(H*G)*(s+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h+
    (4096*ratio*(r+1)*(h+2*H*h+(H*G)*(p+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h)+
    (4096*ratio*(r+1)*(h+2*H*h+(H*G)*(a+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h)+
    (1024*ratio*(r+d.degree+1)*(h+2*H*h+H*G*n)+(115*ratio*r)*(2^(h/2)*h))≤_
  have h₁:=slot s su
  have h₂:=slot p pu
  have h₃:=slot a au
  calc
    _ ≤ 4096*ratio*(r*(2*d.cap)+1)*fill+(2048*ratio)*lookup+
        (4096*ratio*(r+1)*fill+(2048*ratio)*lookup)+
        (4096*ratio*(r+1)*fill+(2048*ratio)*lookup)+
        (1024*ratio*(r+d.degree+1)*fill+(115*ratio*r)*lookup) := by
      simp only [lookup,Nat.mul_assoc] at literal h₁ h₂ h₃ finalRect ⊢
      gcongr
    _ = _ :=by unfold wordCoefficients fill lookup;ring

theorem word_bill_dense (B : Sources) (base w h s p a n U ratio : ℕ)
    (sp : 0<d.signedLanes) (pp : 0<d.paidLanes) (ap : 0<d.aliveLanes) (np : 0<d.lanes)
    (su : s≤U) (pu : p≤U) (au : a≤U) (nu : n≤U) (bus : w≤ratio*h)
    (signed : h≤d.signedLanes*s) (paid : h≤d.paidLanes*p)
    (alive : h≤d.aliveLanes*a) (next : h≤d.lanes*n)
    (sc : d.signedLanes≤h) (pc : d.paidLanes≤h) (nc : d.lanes≤h/2)
    (sb : DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤h/2)
    (pb : d.paidBits*d.paidLanes≤h/2) (ab : d.aliveLanes≤h/2) :
    bitTariff (d.program B base w) (d.ticks B base) ≤
      (d.wordCoefficients ratio).1*(h+2*H*h+2*H*G*U)+
      (d.wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h := by
  exact d.word_bill_rows B base w h s p a n U ratio sp pp ap np su pu au nu bus
    (DescentDatedSeedStartup.chunk_work H G _ h _ signed) (DescentDatedSeedStartup.chunk_work H G _ h _ paid)
    (DescentDatedSeedStartup.chunk_work H G _ h _ alive) (DescentDatedSeedStartup.chunk_work H G _ h _ next) sc pc nc sb pb ab

theorem word_bill (B : Sources) (base w h s p a n U ratio : ℕ)
    (sp : 0<s) (pp : 0<p) (ap : 0<a) (np : 0<n)
    (su : s≤U) (pu : p≤U) (au : a≤U) (nu : n≤U) (room : 2*U≤h) (bus : w≤ratio*h)
    (signed : d.signedLanes=DescentSIMDLookup.lanes h s) (paid : d.paidLanes=DescentSIMDLookup.lanes h p)
    (alive : d.aliveLanes=DescentSIMDLookup.lanes h a) (next : d.lanes=DescentSIMDLookup.lanes h n)
    (sb : DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤h/2)
    (pb : d.paidBits*d.paidLanes≤h/2) (ab : d.aliveLanes≤h/2) :
    bitTariff (d.program B base w) (d.ticks B base) ≤
      (d.wordCoefficients ratio).1*(h+2*H*h+8*H*G*U)+
      (d.wordCoefficients ratio).2*(2*(h+1)^2*2^(h/2))*h := by
  have sw :=(Nat.mul_le_mul_left 2 su).trans room
  have pw :=(Nat.mul_le_mul_left 2 pu).trans room
  have aw :=(Nat.mul_le_mul_left 2 au).trans room
  have nw :=(Nat.mul_le_mul_left 2 nu).trans room
  let fill:=h+2*H*h+8*H*G*U
  let lookup:=2*(h+1)^2*2^(h/2)*h
  have slot (u : ℕ) (l : u≤U) : h+2*H*h+4*(H*G)*(u+n)≤fill := by
    calc
      _ ≤ h+2*H*h+4*(H*G)*(U+U) :=by gcongr
      _ = _ :=by unfold fill;ring
  have head := DescentVenueSlabs.word_bill d.signedShape (d.signedPage B) base w h s n ratio sp sw np nw signed next sb bus
  have pay := DescentVenueSlabs.word_bill d.paidShape (fun i=>B.paid i.val) (d.firstEnd base) w h p n ratio pp pw np nw paid next pb bus
  have actors := DescentVenueSlabs.word_bill d.aliveShape (fun i=>B.alive i.val) (d.secondEnd base) w h a n ratio ap aw np nw alive next
    (by change 1*d.aliveLanes≤h/2;simpa using ab) bus
  have end_ := StageVenueTail.word_bill (d.transported B base) (d.thirdEnd base) d.k H G h n d.degree w ratio np nw bus
  rw [←next] at end_
  have finalRect : h+2*H*h+4*H*G*n≤fill := by
    change h+2*H*h+4*H*G*n≤h+2*H*h+8*H*G*U
    gcongr
    omega
  have literal : 2^(h/2)*h≤lookup :=by
    have first : 1≤2*(h+1)^2 := Nat.succ_le_of_lt (by positivity)
    calc
      _ = 1*(2^(h/2)*h) :=by simp
      _ ≤ (2*(h+1)^2)*(2^(h/2)*h) :=Nat.mul_le_mul_right _ first
      _ = _ :=by unfold lookup;ring
  unfold Date.program Date.ticks
  repeat rw [bitTariff_seq]
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add head pay) actors) end_).trans ?_
  change 4096*ratio*(r*(2*d.cap)+1)*(h+2*H*h+4*(H*G)*(s+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h+
    (4096*ratio*(r+1)*(h+2*H*h+4*(H*G)*(p+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h)+
    (4096*ratio*(r+1)*(h+2*H*h+4*(H*G)*(a+n))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h)+
    (1024*ratio*(r+d.degree+1)*(h+2*H*h+4*H*G*n)+(115*ratio*r)*(2^(h/2)*h))≤_
  have h₁:=slot s su
  have h₂:=slot p pu
  have h₃:=slot a au
  calc
    _ ≤ 4096*ratio*(r*(2*d.cap)+1)*fill+(2048*ratio)*lookup+
        (4096*ratio*(r+1)*fill+(2048*ratio)*lookup)+
        (4096*ratio*(r+1)*fill+(2048*ratio)*lookup)+
        (1024*ratio*(r+d.degree+1)*fill+(115*ratio*r)*lookup) := by
      simp only [lookup,Nat.mul_assoc] at literal h₁ h₂ h₃ finalRect ⊢
      gcongr
    _ = _ :=by unfold wordCoefficients fill lookup;ring

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
