import OAI.Hierarchy.DescentResetRowsAfterSolver
import OAI.Hierarchy.DescentResetFieldPrice

namespace OAI
/-! # Word and bit invoice of the real post-estimator instructions and table stores -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGLPacked DescentGL DescentGLControlCode DescentGLNielsen DescentColonies DescentSIMDLookup
open DescentSixParty.PackedFlow ProtocolRAM
open scoped Fin.CommRing
noncomputable section

theorem pages (H h l b payload : ℕ) (short : (b+b)*2^l≤payload/2) :
    2^chartBits H h l b≤2*(H*2^h+1)+2^(payload/2) := by
  let s:=H*2^h
  have upper : 2^(s.log2+1)≤2*(s+1) := by
    by_cases null : s=0
    · simp [null]
    · have valid:2^s.log2≤ s:=(Nat.le_log2 null).mp le_rfl
      rw [pow_succ]
      omega
  by_cases dom : s.log2+1≤(b+b)*2^l
  · rw [chartBits,max_eq_right dom]
    exact (Nat.pow_le_pow_right (by decide) short).trans (Nat.le_add_left ..)
  · rw [chartBits,max_eq_left (le_of_not_ge dom)]
    exact upper.trans (Nat.le_add_right ..)

theorem header_price (C : Chart) (base H h l b w payload : ℕ) (positive : 0<b)
    (chart : C.bits=chartBits H h l b) (short : (b+b)*2^l≤payload/2)
    (keyBits : (h+l)*(h+l)≤payload/2) :
    let m:=h+l
    let n:=Count m
    let ad:=(controlImage (w:=w) (h:=h) (l:=l) base positive).length+(routes C H h l b w).length
    ad≤(1+n)*2^(payload/2)+n+m*2^h+
      6*n*(2*(H*2^h+1)+2^(payload/2)) := by
  let m:=h+l
  have matrix : keys m≤2^(payload/2) := by
    rw [keys,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) keyBits
  have size : C.page≤2*(H*2^h+1)+2^(payload/2):=by
    simpa only [Chart.page,chart] using pages H h l b payload short
  obtain ⟨low,high⟩:=hardware_lengths (w:=w) (h:=h) (l:=l) (H:=H) base positive C
  dsimp only
  rw [low,high]
  change keys m+Count m+Count m*keys m+m*2^h+6*Count m*C.page≤_
  have grow:=Nat.mul_le_mul_left (Count m) matrix
  have route:=Nat.mul_le_mul_left (6*Count m) size
  rw [Nat.add_mul 1 (Count m), Nat.one_mul]
  dsimp only [m] at matrix grow route ⊢
  omega

theorem clock_price (C : Chart) (base solve : ℕ) (counts : Bank) {D : ℕ} (pair : Fin D→Bank)
    (H h l : ℕ) :
    gatherFee C base solve counts pair H h l≤fieldFactor ((1+D)+(h+l)) (Count (h+l)) (1+12*(h+l))*(1+H*2^h) := by
  let banks:=fieldBanks D h l counts pair (plane base (h+l))
  have fetch (j : ℕ) (active : j<(1+D)+(h+l)) : (channelTerm banks j).work≤7 := by
    simp [channelTerm,active,Expr.work]
  have bill:=gather_reset_price C H ((1+D)+(h+l)) h l (channelTerm banks) (cols base (h+l)) (key base solve (h+l)) fetch
  simpa only [gatherFee,key,DescentExteriorSelectedMatrix.expr_work,Count,banks] using bill

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI
