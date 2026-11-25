import OAI.Hierarchy.DescentRetainedNodeWidths
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # A uniform node-width ceiling for the actual chronological archive -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentKernelHistory DescentInitialHost Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε u : ℝ} {S : AtomSchedule} {k : ℕ}

theorem ResetRates.gate_arity {D n h C f g cut tail : ℕ} (ctl : ResetRates G S k D n h C f g cut tail) :
    max 2 ((2+2*h*C)*ctl.bitsR)≤2^S.capGain := by
  let a:=max 19 (6*(2+21*((2*h+4)*(2*h*C+2)))+1)
  have factor : 2+2*h*C≤a := by
    have hm : 2*h*C+2≤(2*h+4)*(2*h*C+2) := Nat.le_mul_of_pos_left _ (by omega)
    have := Nat.le_max_right 19 (6*(2+21*((2*h+4)*(2*h*C+2)))+1)
    dsimp only [a]
    omega
  have room : a≤2^Nat.clog 2 a := Nat.le_pow_clog (by decide) _
  have bitsR : ctl.bitsR≤2^f := (Nat.le_mul_of_pos_left _ (pow_pos (Nat.two_pow_pos n) 2)).trans ctl.rows
  have joined : max 2 ((2+2*h*C)*ctl.bitsR)≤2^f*2^Nat.clog 2 a := by
    apply max_le
    · calc
        2 ≤ a := (show 2≤19 by decide).trans (Nat.le_max_left ..)
        _ ≤ 2^Nat.clog 2 a := room
        _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    · simpa only [Nat.mul_comm (2^f)] using Nat.mul_le_mul (factor.trans room) bitsR
  rw [←pow_add] at joined
  exact joined.trans (Nat.pow_le_pow_right (by decide : 0<2) (by simpa only [ctl.gain,reserveGain,a] using ctl.cap))

namespace Chronology
variable {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ w hist : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ w hist} {last : Reached W₁ G q ε S k i₁ z₁ D₁ w hist}

theorem Path.grain_le_first (path : Path first last) : z₁≤z₀ := by
  induction path with
  | here=>exact le_rfl
  | ordinary prior ticket ih=>
    rw [ticket.grainStep] at ih
    exact (Nat.le_mul_of_pos_right _ (by have :=G.paid;omega)).trans ih
  | reset prior b ih=>exact ih

theorem Path.widths (p : ℕ) (hp : 0<p) (a : Archive W₀) (path : Path first last) (r : path.whole p)
    {M : ℕ} (pre : a.bit.WidthBound M) (newParty : 8*(z₀*(G.C+G.k+G.b+2))≤M)
    (relay : 2*(z₀*G.b)≤M) (bank : 2^S.capGain*p≤M) : (path.archive p hp a r).bit.WidthBound M := by
  induction path with
  | here=>exact pre
  | @ordinary A i z D z' D' src prior ν he T c n dst ticket ih=>
    have zT : T.z≤z₀ := by rw [ticket.quantum,src.grain]; exact prior.grain_le_first
    apply BitDescription.WidthBound.follow
    apply BitDescription.WidthBound.scanned (ih r)
    exact (Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right _ zT)).trans newParty
  | @reset A i z D n h C f g cut tail src prior ctl b ih=>
    let before:=prior.archive p hp a r.1
    have widths : before.bit.WidthBound M:=ih r.1
    have grains : (BitDescription.granular A b.count (z*G.b) b.fit before.bit).WidthBound M := widths
    apply BitDescription.WidthBound.follow
    apply BitDescription.WidthBound.lane_reset grains
    · intro e
      change 2*(z*G.b)≤M
      exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right G.b prior.grain_le_first)).trans relay
    · rw [b.width]
      exact (Nat.mul_le_mul_right p ctl.gate_arity).trans bank

end Chronology
end
end Hierarchy.DescentSixParty

end OAI
