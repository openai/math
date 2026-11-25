import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentPrivateDonorBillNumbers
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # One uniform address exponent for the selected initial directory -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem seed_directory_at (t f g reset : ℕ) :
    ∃A : ℕ,∀h J M cutoff,1≤h → J≤h → M≤4^h →
      let S:=stageNumbers G t J f g reset M cutoff
      S.copies≤2^h →
        h≤A*h ∧ M≤2^(A*h) ∧ hostRows M≤2^(A*h) ∧ S.copies≤2^(A*h) ∧
        S.length≤2^(A*h) ∧ S.length*S.batch≤2^(A*h) :=by
  let c:=t+1
  let b:=hostRate t reset+capRate G t g
  let A:=14+(b+1)*c
  refine ⟨A,?_⟩
  intro h J M cutoff high age sites S copies
  have one : 1≤A :=by dsimp [A];omega
  have two : 2≤A :=by dsimp [A];omega
  have slot : S.length ≤ c*h :=Nat.mul_le_mul_left c age
  have a₁ : h≤A*h :=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right h one
  have a₂ : 2*h≤A*h :=Nat.mul_le_mul_right h two
  have orig : M≤2^(2*h) :=by simpa only [pow_mul,show (2:ℕ)^2=4 by decide] using sites
  have grid : hostRows M≤2^(2*h) :=Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow orig)
  have c_le : c≤A :=(Nat.le_mul_of_pos_left c (show 0 < b+1 by omega)).trans (Nat.le_add_left ..)
  have lengthBound : S.length≤2^(c*h) :=
    (Nat.lt_two_pow_self (n:=S.length)).le.trans (Nat.pow_le_pow_right (by decide) slot)
  refine ⟨a₁,orig.trans (Nat.pow_le_pow_right (by decide) a₂),grid.trans (Nat.pow_le_pow_right (by decide) a₂),
    copies.trans (Nat.pow_le_pow_right (by decide) a₁),lengthBound.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h c_le)),?_⟩
  have host : (2^(hostRate t reset))^S.length ≤ 2^(hostRate t reset*(c*h)) :=by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ slot)
  have capExp : 11+capRate G t g*S.length ≤ 11*h+capRate G t g*(c*h) :=
    Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ slot)
  have caps :=Nat.pow_le_pow_right (by decide : 0<2) capExp
  change S.length*((M*S.copies)*(2^(hostRate t reset))^S.length*2^(11+capRate G t g*S.length))≤_
  apply (Nat.mul_le_mul lengthBound (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul orig copies) host) caps)).trans
  simp only [←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp only [A,b]
  ring_nf
  exact le_rfl

theorem seed_directory_capacity (t f g reset : ℕ) :
    ∃A : ℕ,∀τ β,∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*β)
      ∀M,let S:=stageNumbers G t J f g reset M (tail τ J)
        M≤4^h → S.copies≤2^h →
        h≤A*h ∧ M≤2^(A*h) ∧ hostRows M≤2^(A*h) ∧ S.copies≤2^(A*h) ∧
        S.length≤2^(A*h) ∧ S.length*S.batch≤2^(A*h) :=by
  obtain ⟨A,room⟩:=seed_directory_at G t f g reset
  refine ⟨A,fun τ β=>?_⟩
  filter_upwards [eventually_ge_atTop 1] with h high
  intro J M S sites copies
  exact room h J M (tail τ J) high ((Nat.div_le_self ..).trans (Nat.log_le_self ..)) sites copies

end Hierarchy.DescentSixParty

end OAI
