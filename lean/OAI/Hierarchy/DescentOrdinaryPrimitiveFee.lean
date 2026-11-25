import OAI.Hierarchy.DescentOrdinaryPalettePaidRows
import OAI.Hierarchy.DescentOrdinaryPaletteBirthFee
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! The complete ordinary immutable-label update in the common per-date paper tariff. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
set_option quotPrecheck false
noncomputable section
variable (L : DescentOrdinaryPrimitiveCheckpoint.Layout)
private def polynomial (blocks lows ports old «fields» N : ℕ) :=
  let T:=lows+1
  let port:=ports*T+(1+(T+ports))
  let count:=blocks*T
  let words:=blocks+2*count
  let K:=1+N*61
  let spread:=(4+lows*(4+T*(2*K+4)))+((4+10*words)+(4+count*54))+
    7*((15+lows*(11+4*K))+(15*(words+1)+111))
  let join:=(4+10*(2*1))+(4+blocks*(4+T*(2*25+4)))+7*((15*(2*1+1))+(15+blocks*(11+4*25)))
  retileFactor blocks lows+retileFactor «fields» lows+retileFactor blocks lows+literalFee port+
    (literalFee old+literalFee ((3+N)*2))+spread+join+retileFactor blocks lows

theorem factor_polynomial (a : ℕ) (blocks : L.blocks≤a) (lows : L.lows≤a) (ports : L.ports≤a)
    (old : L.oldNodes≤a) («fields» : L.fields≤a) (N : L.candidates≤a) : L.wordFactor≤2^20*(a+1)^3:=by
  change polynomial L.blocks L.lows L.ports L.oldNodes L.fields L.candidates≤_
  calc
    _ ≤ polynomial a a a a a a:=by
      dsimp only [polynomial, retileFactor, literalFee]
      gcongr
    _ ≤ _ :=by unfold polynomial retileFactor literalFee; ring_nf; omega

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentCompiler.TerminalScale DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (A : ArgumentEntry v) (match_ : A.Match v floor)
    (radix : v.vector.radix=2^v.reference.k) (w h ratio unit : ℕ)
local notation "L" => v.paletteShape
local notation "B" => v.bornBook

def primitiveFactor :=2048*(DescentOrdinaryPaletteBirth.fields v.bornBook+1)+v.paletteShape.wordFactor

/-- A single fixed rate covers the local rectangular construction at every eligible age. -/
theorem primitive_factor_rate (J k₀ : ℕ) (blocks : (L).blocks≤ scale J k₀)
    (lows : (L).lows≤ scale J k₀) (ports : (L).ports≤ scale J k₀) (old : (L).oldNodes≤ scale J k₀)
    («fields» : (L).fields≤ scale J k₀) (N : (L).candidates≤ scale J k₀)
    (born : DescentOrdinaryPaletteBirth.fields (B)≤ scale J k₀) : v.primitiveFactor≤ scale J (25+3*k₀):=by
  let a:=scale J k₀
  have one : 1≤a:=Nat.two_pow_pos _
  have cube : a+1≤2*a:=by omega
  have bd:=(L).factor_polynomial a blocks lows ports old «fields» N
  have real : v.primitiveFactor≤2^25*a^3:=by
    unfold primitiveFactor
    have low : a ≤ a^3 := by
      calc
        a ≤ a * a := Nat.le_mul_of_pos_left _ one
        _ ≤ a^3 := by simpa only [pow_succ,pow_zero,Nat.one_mul] using Nat.le_mul_of_pos_right (a*a) one
    change DescentOrdinaryPaletteBirth.fields (B) ≤ a at born
    nlinarith only [born,bd,Nat.pow_le_pow_left cube 3,low,pow_pos (by omega : 0<a) 3]
  have limit : 25+3*(k₀*(J+1))≤(25+3*k₀)*(J+1):=by nlinarith
  calc
    _ ≤ _ := real
    _ = 2^(25+3*(k₀*(J+1))):=by simp only [a,scale,Nat.pow_add,←pow_mul];congr 2; ring
    _ ≤ _ :=Nat.pow_le_pow_right (by decide : 0<2) limit

theorem primitive_word_fee (room : (L).Funding h unit) (hosts : 0<(L).hosts) (lows : 0<(L).lows)
    (hEq : (B).hosts=(L).hosts) (gEq : (B).groups=(L).oldGroups)
    (chip : 2*(B).chipBits*(B).lanes≤h/2) (bus : w≤ratio*h) :
    invoice (v.primitiveUpdate floor A match_ radix w)*w≤ratio*v.primitiveFactor*(L).volume h unit:=by
  have birth:=DescentOrdinaryPaletteBirth.scaled v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor
    (B) (v.operandEnd floor) w h ratio unit (A.chipBank v floor) chip room.newborn.occupied bus
  let first:=2048*(DescentOrdinaryPaletteBirth.fields (B)+1)
  have large : 2^(h/2)*h≤Layout.control h:=by
    unfold Layout.control
    have en : 1≤(h+1)^2:=Nat.one_le_pow _ _ (by omega)
    nlinarith only [Nat.mul_le_mul_right (2^(h/2)*h) en]
  have early : invoice (v.primitiveBirth floor A w)*w≤ratio*first*(L).volume h unit:=by
    simp only [hEq,gEq] at birth
    unfold Layout.volume Layout.liveVolume
    apply birth.trans
    dsimp only [first]
    nlinarith only [Nat.mul_le_mul_left (ratio * (2048 * (DescentOrdinaryPaletteBirth.fields (B) + 1))) large]
  have next:=(L).paid_le (v.primitiveFirst (v.operandEnd floor)) (v.primitiveSources floor A match_ radix)
    (w:=w) room.old.positive room.newborn.positive room.ranks.positive room.working.positive room.held.positive
  have later:=(L).word_fee h unit room hosts lows
  rw [primitiveUpdate,invoice_seq,Nat.add_mul]
  calc
    _≤ratio*first*(L).volume h unit+((L).paid*(ratio*h)):=Nat.add_le_add early (Nat.mul_le_mul next bus)
    _≤ratio*v.primitiveFactor*(L).volume h unit:=by
      dsimp only [primitiveFactor,first]
      nlinarith only [Nat.mul_le_mul_left ratio later]

/-- Requested split into the live host/traffic term and one literal half-word page pool.
The loss depends on the bounded local cone at this date only. -/
theorem primitive_scaled (J a u : ℕ) (room : (L).Funding h unit) (hosts : 0<(L).hosts) (lows : 0<(L).lows)
    (hEq : (B).hosts=(L).hosts) (gEq : (B).groups=(L).oldGroups)
    (chip : 2*(B).chipBits*(B).lanes≤h/2) (bus : w≤ratio*h)
    (factor : v.primitiveFactor≤ scale J a) (unitRate : unit≤ scale J u) :
    invoice (v.primitiveUpdate floor A match_ radix w)*w≤
      ratio*scale J (a+u+1)*((L).hosts*h+(L).hosts*(L).groups*(L).blocks)+
      ratio*scale J (a+u+1)*Layout.control h:=by
  have pay:=v.primitive_word_fee floor A match_ radix w h ratio unit room hosts lows hEq gEq chip bus
  have yu:1≤ scale J u:=Nat.two_pow_pos _
  have yh:h≤(L).hosts*h:=Nat.le_mul_of_pos_left _ hosts
  have c:1≤ scale J 1:=Nat.two_pow_pos _
  have cc:2≤ scale J 1:=by simpa only [scale,Nat.one_mul,pow_one] using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤J+1)
  have a':=Nat.mul_le_mul factor unitRate
  have d':=Nat.mul_le_mul factor yu
  have m':2*(v.primitiveFactor)≤ scale J (a+u+1):=by
    rw [←scale_mul,←scale_mul]
    nlinarith only [Nat.mul_le_mul (Nat.mul_le_mul factor yu) cc]
  have big:v.primitiveFactor*unit≤ scale J (a+u+1):=by
    rw [←scale_mul,←scale_mul]
    exact a'.trans (Nat.le_mul_of_pos_right _ c)
  calc
    _ ≤ _ := pay
    _ ≤ _ :=by
      unfold Layout.volume Layout.liveVolume Layout.oldGroups
      nlinarith only [Nat.mul_le_mul_left (ratio*v.primitiveFactor) yh,
        Nat.mul_le_mul_left (ratio*((L).hosts*h)) m',Nat.mul_le_mul_left (ratio*((L).hosts*(L).groups*(L).blocks)) big,
        Nat.mul_le_mul_left (ratio*Layout.control h) (show v.primitiveFactor≤ scale J (a+u+1) by omega)]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
