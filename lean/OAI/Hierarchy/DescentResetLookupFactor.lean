import OAI.Hierarchy.DescentResetSelectedLookupVolume

namespace OAI
/-! A uniform polynomial for the processes controlled by local operand and node counts. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentResetRankedWindows DescentCompiler.TerminalScale DescentResetCandidatePair
noncomputable section
variable (v : ResetOutput)

private def envelope (n : ℕ) :=
  let U:=120+(n+4+n)*261
  let F:=Layout.finalWork n 7
  scanFactor (n*n) n+scanFactor (n*n) 7+12000+120*3+
  (120*(4*n+1)+scanFactor n (visit U (U+12) 7 F n))+
  (120*(n+2)+scanFactor n (1+n*18))+
  120*(7+(2*n+1)+(2*(n+1)+1)+(2*(n+2)+1)+11+
    (2*(4+n)+1)+(2*(4+7*n)+1)+(2*(n+n)+1)+(2*(n+7*n)+1))

theorem lookup_factor_polynomial (header n : ℕ) (p : v.LookupLimits header n) :
    v.lookupFactor header≤1000000000*(n+1)^4:=by
  obtain ⟨u,j,pub,m,pages,cols,K,X,head⟩:=p
  apply Nat.le_trans (m:=envelope n)
  · unfold lookupFactor envelope DescentResetOperandSetup.Chart.selectorWork DescentResetOperandSetup.Chart.tableFactor
      scanFactor visit Layout.finalWork Layout.pullWork Layout.pairWork
    dsimp only
    gcongr
  · unfold envelope Layout.finalWork
    rcases le_total 7 (Layout.pullWork n 7) with lo|hi
    · rw [max_eq_right lo]
      unfold scanFactor visit Layout.pullWork Layout.pairWork
      ring_nf
      omega
    · rw [max_eq_left hi]
      unfold scanFactor visit
      ring_nf
      omega

theorem lookup_factor_rate (r : ℕ) :
    ∀j header, v.LookupLimits header (scale j r) →v.lookupFactor header≤ scale j (30+4*(r+1)):=by
  intro j header small
  have one:1≤ scale j r:=Nat.two_pow_pos _
  have enough:scale j r+1≤ scale j (r+1):=by
    have two:2≤2^(j+1):=by
      change 2^1≤2^(j+1)
      exact Nat.pow_le_pow_right (by decide) (show 1≤j+1 by omega)
    calc
      scale j r+1≤ scale j r*2:=by omega
      _≤ scale j r*2^(j+1):=Nat.mul_le_mul_left _ two
      _=scale j (r+1):=by simp [scale,Nat.add_mul,pow_add]
  apply (v.lookup_factor_polynomial _ _ small).trans
  have constant:1000000000≤2^(30*(j+1)):=
    (by decide : 1000000000≤2^30).trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    1000000000*(scale j r+1)^4≤2^(30*(j+1))*(scale j (r+1))^4:=
      Nat.mul_le_mul constant (Nat.pow_le_pow_left enough _)
    _=scale j (30+4*(r+1)):=by
      unfold scale
      rw [←pow_mul,←pow_add]
      congr 1
      ring

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
