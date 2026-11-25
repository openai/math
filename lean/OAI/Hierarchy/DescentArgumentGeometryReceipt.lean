import OAI.Hierarchy.DescentArgumentRowVolume
import OAI.Hierarchy.DescentOrdinarySharedLedger

namespace OAI
/-! # Amortizing a full registered ordinary argument calendar at the original number of input sites -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open Filter DescentCompiler DescentCompiler.TerminalScale
noncomputable section
variable {F : Type} [Field F] {P : Type}

theorem SectionPopulation.shared_control_all (ratio exponent saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(Pin : Type) (v : PhysicalOrdinary F Pin) (A : ArgumentEntry v) (S : AtomSchedule)
      (age J original cost : ℕ),SectionPopulation v A S age→0 < S.hostSize age→
      J ≤ Nat.log 2 h→2^h ≤ original→cost ≤ scale J exponent*ratio*v.rowVolume h→
      let growth:=5+2*(2^S.hostGain)*(S.radix+1)
      let coefficient:=scale J exponent*ratio*growth
      cost ≤ S.hostSize age*h*coefficient+S.hostSize age*S.groupCount age*coefficient+
        original/(2^J)^saving :=by
  filter_upwards [shared_date ratio exponent 1 saving] with h reserve
  intro Pin v A S age J original cost sites live ageBound population paid growth coefficient
  let H:=S.hostSize age
  let G:=S.groupCount age
  let Q:=2^(h/2)
  let fq:=scale J exponent*ratio
  have area:=sites.row_volume h live
  have before : cost ≤ fq*(growth*(H*h+H*G)+(h+1)^2*Q*h):=
    paid.trans (Nat.mul_le_mul_left fq area)
  apply reserve J original H G coefficient coefficient cost (exponent*(J+1)) ageBound
    (by simp only [pow_one];exact le_rfl) population
  calc
    cost ≤ fq*(growth*(H*h+H*G)+(h+1)^2*Q*h):=before
    _=H*h*coefficient+H*G*coefficient+(ratio*2^(exponent*(J+1)))*((h+1)^2*Q)*h:=by
      dsimp only [coefficient,fq,scale]
      ring
    _≤_:=by dsimp only [Q];gcongr;omega


theorem SectionPopulation.shared_control (ratio exponent saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(v : PhysicalOrdinary F P) (A : ArgumentEntry v) (S : AtomSchedule)
      (age J original cost : ℕ),SectionPopulation v A S age→0 < S.hostSize age→
      J ≤ Nat.log 2 h→2^h ≤ original→cost ≤ scale J exponent*ratio*v.rowVolume h→
      let growth:=5+2*(2^S.hostGain)*(S.radix+1)
      let coefficient:=scale J exponent*ratio*growth
      cost ≤ S.hostSize age*h*coefficient+S.hostSize age*S.groupCount age*coefficient+
        original/(2^J)^saving :=by
  filter_upwards [shared_date ratio exponent 1 saving] with h reserve
  intro v A S age J original cost sites live ageBound population paid growth coefficient
  let H:=S.hostSize age
  let G:=S.groupCount age
  let Q:=2^(h/2)
  let fq:=scale J exponent*ratio
  have area:=sites.row_volume h live
  have before : cost ≤ fq*(growth*(H*h+H*G)+(h+1)^2*Q*h):=
    paid.trans (Nat.mul_le_mul_left fq area)
  apply reserve J original H G coefficient coefficient cost (exponent*(J+1)) ageBound
    (by simp only [pow_one];exact le_rfl) population
  calc
    cost ≤ fq*(growth*(H*h+H*G)+(h+1)^2*Q*h):=before
    _=H*h*coefficient+H*G*coefficient+(ratio*2^(exponent*(J+1)))*((h+1)^2*Q)*h:=by
      dsimp only [coefficient,fq,scale]
      ring
    _≤_:=by dsimp only [Q];gcongr;omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
