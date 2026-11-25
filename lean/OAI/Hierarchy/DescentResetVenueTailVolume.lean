import OAI.Hierarchy.DescentPublishedVenueInvoice
import OAI.Hierarchy.DescentDatedResetVenuePrice
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Scalar bounds on the tariffs recorded in a reset venue's accounting record. -/
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup DescentPackedColony

theorem tariff_volume (s : Shape) (h V : ℕ) (old : s.sourceLanes ≤ h) (next : s.targetLanes ≤ h)
    (key : s.bits*s.sourceLanes ≤ h/2)
    (rows : 1+s.hosts*chunks s.groups s.sourceLanes+s.hosts*chunks s.groups s.targetLanes ≤ V)
    (shared : (h+1)^2*2^(h/2) ≤ V) :
    tariff s ≤ 4096*(s.pages+2)*V := by
  have table:=Overlap.half_pages h s.groups s.sourceLanes s.targetLanes s.bits old next key
  calc
    _ ≤ _ := tariff_split s
    _ ≤ 4096*(s.pages+1)*V+2048*(2*V) := by
      apply Nat.add_le_add (Nat.mul_le_mul_left _ rows)
      apply Nat.mul_le_mul_left
      exact table.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 shared)
    _ = _ := by ring
end Hierarchy.DescentVenueSlabs

namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentSIMDLookup
variable (d : Date)

def resetFactor :=4096*((2^d.k*(2*d.cap)+2)+2*(2^d.k+2))+1024*(2^d.k+d.degree+1)+115*2^d.k

theorem reset_tariff (h A V : ℕ) (signed : d.signedLanes=A) (paid : d.paidLanes=A) (alive : d.aliveLanes=A)
    (before : A ≤ h) (source : DescentSignedCableCodec.width d.degree d.cap*A ≤ h/2)
    (cash : d.paidBits*A ≤ h/2) (one : A ≤ h/2) (after : d.lanes ≤ h/2)
    (row : 1+d.hosts*chunks d.groups A+d.hosts*chunks d.groups d.lanes ≤ V)
    (family : 1+d.hosts+d.hosts*chunks d.groups d.lanes ≤ V)
    (shared : (h+1)^2*2^(h/2) ≤ V) : d.tariff ≤ d.resetFactor*V := by
  have last:d.lanes ≤ h:=after.trans (Nat.div_le_self ..)
  have s₀:=DescentVenueSlabs.tariff_volume d.signedShape h V (by simpa only [signedShape,signed] using before) last
    (by simpa only [signedShape,signed] using source) (by simpa only [signedShape,signed] using row) shared
  have s₁:=DescentVenueSlabs.tariff_volume d.paidShape h V (by simpa only [paidShape,paid] using before) last
    (by simpa only [paidShape,paid] using cash) (by simpa only [paidShape,paid] using row) shared
  have s₂:=DescentVenueSlabs.tariff_volume d.aliveShape h V (by simpa only [aliveShape,alive] using before) last
    (by simpa only [aliveShape,alive,Nat.one_mul] using one) (by simpa only [aliveShape,alive] using row) shared
  have table:2^d.lanes ≤ V:=(Nat.pow_le_pow_right (by decide : 0 < 2) after).trans
    ((Nat.le_mul_of_pos_left _ (by positivity : 0 < (h+1)^2)).trans shared)
  have s₃:StageVenueTail.tariff d.k d.hosts d.groups d.lanes d.degree ≤
      1024*(2^d.k+d.degree+1)*V+115*2^d.k*V:=
    (StageVenueTail.tariff_split ..).trans (Nat.add_le_add (Nat.mul_le_mul_left _ family) (Nat.mul_le_mul_left _ table))
  calc
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add s₀ s₁) s₂) s₃
    _ = _ := by dsimp only [resetFactor,signedShape,paidShape,aliveShape];ring
end Hierarchy.DescentSixParty.StageVenueTail.Date

namespace Hierarchy.DescentCompactVenuePeers
open DescentVenueQuantityPlanes
noncomputable section

def compactFactor:=10000*(1+rowWork+hubWork)

theorem compact_fee (raw H : ℕ) : fee raw H ≤ compactFactor*(1+raw+H) := by
  have a:span raw ≤ 2*(raw+1)+1:=DescentDyadicSpan.span_le (raw+1)
  have b:span (3*H) ≤ 2*(3*H+1)+1:=DescentDyadicSpan.span_le (3*H+1)
  unfold fee tableScanBill book compactFactor
  nlinarith only [a,b,Nat.zero_le (rowWork*raw),Nat.zero_le (hubWork*raw),Nat.zero_le (rowWork*H),
    Nat.zero_le (hubWork*H),Nat.zero_le raw,Nat.zero_le H]
end
end Hierarchy.DescentCompactVenuePeers

end OAI
