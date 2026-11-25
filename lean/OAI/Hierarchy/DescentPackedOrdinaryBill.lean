import OAI.Hierarchy.DescentMatcherRatePolynomials
import OAI.Hierarchy.DescentPackedMatchChooserInput
import OAI.Hierarchy.DescentPackedMatchInvoice

namespace OAI
/-! # The bit cost of the complete ordinary census, chooser and packed matching pass -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM
noncomputable section

/-- This bound includes both printed static tables, the host-order scan and all
original selector profile reads. The per-stage volume has one width for each
physical host and one lane width for each group at each host. -/
theorem ordinary_bill_of_page_bits (s : Shape) (k D cap a d K H G payload W ratio unit seats base matcher original b quota : ℕ)
    (chooser : Chooser.Layout) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart) (P : Ports D)
    (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (positive : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload)
    (memory : 2^(payload/2)*payload≤original) (gate : 2^k+a≤unit) (cable : DescentSignedCableCodec.width D cap≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let chooserTicks:=chooser.ticks D k b quota H G M W
    let matchTicks:=((4+10*Prepare.staticWords k D cap a M H G)+clock (Prepare.passes C Z base H G M D))+
      Gather.ROM.ticks s d r D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
    (chooserTicks+matchTicks)*W ≤ ratio*(ordinaryFactor k D cap K*(payload+H*payload+4*H*G*unit+original)) := by
  let M:=lanes payload unit
  let r:=(2:ℕ)^k
  let n:=«fields» r D (2*cap)
  let pages:=(1+n)+(K+6)
  let blocks:=r+r*(2*cap)
  let packed:=H*payload+4*H*G*unit
  let total:=payload+H*payload+4*H*G*unit+original
  let chooserTicks:=chooser.ticks D k b quota H G M W
  let matchTicks:=((4+10*Prepare.staticWords k D cap a M H G)+clock (Prepare.passes C Z base H G M D))+
    Gather.ROM.ticks s d r D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
  have first : chooserTicks*W≤ratio*((96+Phase.factor k D)*(payload+packed)) := by
    simpa only [chooserTicks,Chooser.Layout.ticks,packed,Nat.add_assoc] using
      Phase.census_phase_bill_at_unit k payload W ratio D H G unit (chooser.shelves D k b M)
        (chooser.census k b quota H G M false) (chooser.census k b quota H G M true) positive wide hardware
  have second:=Prepared.total_price_of_page_bits s k D cap a d K H G payload W ratio unit seats base matcher original
    C Z P wins marked positive wide hardware memory gate cable
  change matchTicks*W≤ratio*((8+20*H*D)*payload+10*(r+2+pages)*original+10*(2+K)*packed+
    ((8+H*D*(200*(D+1)^3+4)+4*blocks)*payload+54*blocks*packed)+
    ((432+4*K)*payload+K*(668+112*n)*packed)) at second
  have single : payload≤total := by dsimp only [total];omega
  have host : H*payload≤total := by dsimp only [total];omega
  have group : packed≤total := by dsimp only [total,packed];omega
  have both : payload+packed≤total := by dsimp only [total,packed];omega
  have rom : original≤total := by dsimp only [total];omega
  change (chooserTicks+matchTicks)*W≤ratio*(ordinaryFactor k D cap K*total)
  rw [Nat.add_mul]
  apply (Nat.add_le_add first second).trans
  rw [← Nat.mul_add]
  apply Nat.mul_le_mul_left
  change (96+Phase.factor k D)*(payload+packed)+
    ((8+20*H*D)*payload+10*(r+2+pages)*original+10*(2+K)*packed+
    ((8+H*D*(200*(D+1)^3+4)+4*blocks)*payload+54*blocks*packed)+
    ((432+4*K)*payload+K*(668+112*n)*packed)) ≤
    (96+Phase.factor k D+(8+20*D)+10*(r+2+pages)+10*(2+K)+
    (8+D*(200*(D+1)^3+4)+4*blocks)+54*blocks+(432+4*K)+K*(668+112*n))*total
  nlinarith only [Nat.mul_le_mul_left (96+Phase.factor k D) both,
    Nat.mul_le_mul_left 8 single,Nat.mul_le_mul_left (20*D) host,
    Nat.mul_le_mul_left (10*(r+2+pages)) rom,Nat.mul_le_mul_left (10*(2+K)) group,
    Nat.mul_le_mul_left (D*(200*(D+1)^3+4)) host,Nat.mul_le_mul_left (4*blocks) single,
    Nat.mul_le_mul_left (54*blocks) group,Nat.mul_le_mul_left (432+4*K) single,
    Nat.mul_le_mul_left (K*(668+112*n)) group]

theorem ordinary_bill (s : Shape) (k D cap a d K H G payload W ratio unit seats base matcher original b quota : ℕ)
    (chooser : Chooser.Layout) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart) (P : Ports D)
    (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (positive : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload)
    (memory : 2^payload≤original) (gate : 2^k+a≤unit) (cable : DescentSignedCableCodec.width D cap≤unit) :
    let M:=lanes payload unit
    let r:=(2:ℕ)^k
    let chooserTicks:=chooser.ticks D k b quota H G M W
    let matchTicks:=((4+10*Prepare.staticWords k D cap a M H G)+clock (Prepare.passes C Z base H G M D))+
      Gather.ROM.ticks s d r D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
    (chooserTicks+matchTicks)*W ≤ ratio*(ordinaryFactor k D cap K*(payload+H*payload+4*H*G*unit+original)) :=
  ordinary_bill_of_page_bits s k D cap a d K H G payload W ratio unit seats base matcher original b quota
    chooser C Z P wins marked positive wide hardware (Prepared.page_bits memory) gate cable

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
