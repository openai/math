import OAI.Hierarchy.DescentResetRankedWindowVolume
import OAI.Hierarchy.DescentDatedLocalScale

namespace OAI
/-! # Structural and dyadic rates of the actual ranked-window invoice -/
namespace Hierarchy.DescentResetRankedWindows.Layout
open DescentResetSignedScan DescentDatedAddressBook DescentCompiler.TerminalScale

private theorem rank_mono {X K c l Y J d m : ℕ} (x : X≤Y) (k : K≤J) (h : c≤d) (t : l≤ m) :
    rankedFactor X K c l ≤ rankedFactor Y J d m := by
  unfold rankedFactor panelFactor scanFactor scanNames originalWork prefixWork signedTermWork signedFieldWork
    finalWork keyWork pullWork pairWork Ranks.count DescentNextSignedWindow.Native.All.count
    DescentResetSourceTicketBank.expressionCost
  gcongr

theorem rankedFactor_polynomial {X K cap lim n : ℕ} (x : X≤n) (k : K≤n) (c : cap≤n) (t : lim≤n) :
    rankedFactor X K cap lim ≤ 10000000*(n+1)^5 := by
  apply (rank_mono x k c t).trans
  unfold rankedFactor panelFactor scanFactor scanNames originalWork prefixWork signedTermWork signedFieldWork
    finalWork keyWork Ranks.count DescentNextSignedWindow.Native.All.count DescentResetSourceTicketBank.expressionCost
  rcases le_total 7 (pullWork n n) with hi|lo
  · rw [max_eq_right hi]
    unfold pullWork pairWork
    ring_nf
    omega
  · rw [max_eq_left lo]
    unfold pullWork pairWork
    ring_nf
    omega

/-- All four local inputs may vary with the selected date. -/
theorem ranked_factor_rate (r : ℕ) :
    ∃e,∀j X K cap lim, X≤ scale j r → K≤ scale j r → cap≤ scale j r → lim≤ scale j r →
      rankedFactor X K cap lim ≤ scale j e := by
  refine ⟨24+5*(r+1),?_⟩
  intro j X K cap lim x k c t
  have one : 1≤ scale j r := Nat.two_pow_pos _
  have step : scale j r+1 ≤ scale j (r+1) := by
    have two : 2≤2^(j+1) := (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤j+1))
    calc scale j r+1 ≤ scale j r*2 := by omega
         _ ≤ scale j r*2^(j+1) := Nat.mul_le_mul_left _ two
         _ = scale j (r+1) := by simp [scale,Nat.add_mul,pow_add]
  have fixed : 10000000≤2^(24*(j+1)) :=
    (by decide : 10000000≤2^24).trans (Nat.pow_le_pow_right (by decide) (by omega))
  apply (rankedFactor_polynomial x k c t).trans
  calc
    10000000*(scale j r+1)^5 ≤ 2^(24*(j+1))*(scale j (r+1))^5 :=
      Nat.mul_le_mul fixed (Nat.pow_le_pow_left step 5)
    _ = scale j (24+5*(r+1)) := by
      unfold scale
      rw [←pow_mul,←pow_add]
      congr 1
      ring

end Hierarchy.DescentResetRankedWindows.Layout

end OAI
