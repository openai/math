import OAI.Hierarchy.DescentPackedMatchPrepared

namespace OAI
/-! # Bit price of the two physical initializer and scan phases -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
open DescentSIMDLookup ProtocolRAM DescentPackedPayloadBudget DescentPackedColony
open scoped Classical
noncomputable section

theorem page_bits {payload original : ℕ} (fund : 2^payload≤original) :
    2^(payload/2)*payload≤original := by
  simpa only [Nat.one_mul] using table_bits (words:=2^(payload/2)) (W:=payload) (C:=1) le_rfl (by simp) fund

/-- Bits for the literal writes which initialize both finite tables and all masks. -/
theorem static_price_of_page_bits (k D p a _d K H G W payload unit ratio original : ℕ)
    (occupied : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload) (budget : 2^(payload/2)*payload≤original)
    (gate : 2^k+a≤unit) (wire : DescentSignedCableCodec.width D p≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let pages:=((1+«fields» r D (2*p))+(K+6))
    let cost:=(4+10*Prepare.staticWords k D p a M H G)+(4+10*Gather.ROM.size («fields» r D (2*p)) K H G M unit)
    cost*W≤ratio*((8+20*H*D)*payload+10*(r+2+pages)*original+
      10*(2+K)*(H*payload+4*H*G*unit)) := by
  let M:=lanes payload unit
  let r:=(2:ℕ)^k
  let pages:=((1+«fields» r D (2*p))+(K+6))
  let P:=(2:ℕ)^(payload/2)
  let n:=H*chunks G M
  have packed : unit*M≤payload/2 := by simpa only [Nat.mul_comm unit] using lanes_fit payload unit
  have narrow {a : ℕ} (h : a≤unit) : 2^(a*M)≤P := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right M h).trans packed)
  have first:=narrow (show 1*r≤unit by omega)
  have second:=narrow (show 1*r+a≤unit by omega)
  have third:=narrow wire
  have page : Gather.ROM.pitch unit M≤P := Nat.pow_le_pow_right (by decide) packed
  have setup : Prepare.staticWords k D p a M H G≤(r+2)*P+n+2*H*D := by
    change 2^((1*r)*M)+r*2^((1*r+a)*M)+2^(DescentSignedCableCodec.width D p*M)+n+2*H*D≤_
    nlinarith only [first,Nat.mul_le_mul_left r second,third]
  have dict : Gather.ROM.size («fields» r D (2*p)) K H G M unit≤pages*P+(1+K)*n := by
    change pages*Gather.ROM.pitch unit M+n+(K*H)*chunks G M≤_
    dsimp only [n]
    nlinarith only [Nat.mul_le_mul_left pages page]
  have pagePrice : P*payload≤original := budget
  have scanPrice : n*payload≤H*payload+4*H*G*unit:=volume H G payload unit occupied wide
  apply DescentPackedPayloadBudget.clock hardware
  have start:=Nat.mul_le_mul_right payload setup
  have table:=Nat.mul_le_mul_right payload dict
  have fundedPage := Nat.mul_le_mul_left (10*(r+2+pages)) pagePrice
  have fundedScan := Nat.mul_le_mul_left (10*(2+K)) scanPrice
  dsimp only [M, n, r, pages, P] at start table fundedPage fundedScan ⊢
  nlinarith only [start, table, fundedPage, fundedScan]

theorem static_price (k D p a d K H G W payload unit ratio original : ℕ)
    (occupied : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload) (budget : 2^payload≤original)
    (gate : 2^k+a≤unit) (wire : DescentSignedCableCodec.width D p≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let pages:=((1+«fields» r D (2*p))+(K+6))
    let cost:=(4+10*Prepare.staticWords k D p a M H G)+(4+10*Gather.ROM.size («fields» r D (2*p)) K H G M unit)
    cost*W≤ratio*((8+20*H*D)*payload+10*(r+2+pages)*original+
      10*(2+K)*(H*payload+4*H*G*unit)) :=
  static_price_of_page_bits k D p a d K H G W payload unit ratio original
    occupied wide hardware (page_bits budget) gate wire

theorem prepare_price (k D cap H G payload W ratio unit : ℕ) (C : Prepare.Chart k cap)
    (Z : DescentSortedRoster.Chart) (base : ℕ) (positive : 0<unit) (wide : 2*unit≤payload)
    (hardware : W≤ratio*payload) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    (clock (Prepare.passes C Z base H G M D))*W≤ratio*(
      (8+H*D*(200*(D+1)^3+4)+4*(r+r*(2*cap)))*payload+
      54*(r+r*(2*cap))*(H*payload+4*H*G*unit)) := by
  let M:=lanes payload unit
  let r:=(2:ℕ)^k
  have gas:=Prepare.clock_bound (D:=D) C Z base H G M
  have vol:=volume H G payload unit positive wide
  apply DescentPackedPayloadBudget.clock hardware
  have passCost := Nat.mul_le_mul_right payload gas
  have volumeCost := Nat.mul_le_mul_left (54*(r+r*(2*cap))) vol
  dsimp only [M, r] at passCost volumeCost ⊢
  nlinarith only [passCost, volumeCost]

/-- The input uses native mask, roster and winner preparation, and the same lane
count pays every subsequent source, matching and profile window scan. -/
theorem total_price_of_page_bits (s : Shape) (k D cap a d K H G payload W ratio unit seats base matcher original : ℕ)
    (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart) (P : Ports D)
    (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (positive : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload) (budget : 2^(payload/2)*payload≤original)
    (gate : 2^k+a≤unit) (wire : DescentSignedCableCodec.width D cap≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let N:=«fields» r D (2*cap)
    let pages:=((1+N)+(K+6))
    let vol:=H*payload+4*H*G*unit
    let gas:=((4+10*Prepare.staticWords k D cap a M H G)+clock (Prepare.passes C Z base H G M D))+
      Gather.ROM.ticks s d r D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
    gas*W≤ratio*((8+20*H*D)*payload+10*(r+2+pages)*original+10*(2+K)*vol+
      ((8+H*D*(200*(D+1)^3+4)+4*(r+r*(2*cap)))*payload+54*(r+r*(2*cap))*vol)+
      ((432+4*K)*payload+K*(668+112*N)*vol)) := by
  let M:=lanes payload unit
  let n:=(K*H)*chunks G M
  let r:=(2:ℕ)^k
  let N:=«fields» r D (2*cap)
  let place:=Gather.ROM.place s d r D (2*cap) K H G M unit matcher seats
  let menu:=Gather.ROM.chart s d r D (2*cap) K H G M (M*s.pairs) unit matcher place.source
  have fixed:=static_price_of_page_bits k D cap a d K H G W payload unit ratio original positive wide hardware budget gate wire
  have init:=prepare_price k D cap H G payload W ratio unit C Z base positive wide hardware
  have matchCost:=Gather.stage_fee s d H G payload W ratio unit menu.joins menu.desc menu.mask wins marked P place.source.base
    positive wide hardware
  have sumCosts {a b c d w r x y z : ℕ} (f : (a+c)*w ≤ r*x)
      (i : b*w ≤ r*y) (g : d*w ≤ r*z) : ((a+b)+(c+d))*w ≤ r*((x+y)+z) := by
    calc
      _ = ((a+c)*w + b*w)+d*w := by ring
      _ ≤ (r*x+r*y)+r*z := Nat.add_le_add (Nat.add_le_add f i) g
      _ = _ := by ring
  exact sumCosts fixed init matchCost

theorem total_price (s : Shape) (k D cap a d K H G payload W ratio unit seats base matcher original : ℕ)
    (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart) (P : Ports D)
    (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (positive : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload) (budget : 2^payload≤original)
    (gate : 2^k+a≤unit) (wire : DescentSignedCableCodec.width D cap≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let N:=«fields» r D (2*cap)
    let pages:=((1+N)+(K+6))
    let vol:=H*payload+4*H*G*unit
    let gas:=((4+10*Prepare.staticWords k D cap a M H G)+clock (Prepare.passes C Z base H G M D))+
      Gather.ROM.ticks s d r D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
    gas*W≤ratio*((8+20*H*D)*payload+10*(r+2+pages)*original+10*(2+K)*vol+
      ((8+H*D*(200*(D+1)^3+4)+4*(r+r*(2*cap)))*payload+54*(r+r*(2*cap))*vol)+
      ((432+4*K)*payload+K*(668+112*N)*vol)) :=
  total_price_of_page_bits s k D cap a d K H G payload W ratio unit seats base matcher original
    C Z P wins marked positive wide hardware (page_bits budget) gate wire

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
