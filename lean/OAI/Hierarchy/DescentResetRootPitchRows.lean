import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentPackedCanvasCopy

namespace OAI
/-! # Paying the complete original row at the clipped root and receiver pitch -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentPackedWalsh DescentSIMDLookup
noncomputable section

theorem dyadic_chunks (c e : ℕ) (cut : e≤c) : chunks (2^c) (2^e)=2^(c-e) :=
  PackedFlow.Canvas.original_chunks (u:=c-e) (l:=e) (k:=0)
    (by simp [Nat.sub_add_cancel cut]) (by simp) (Nat.two_pow_pos _)

/-- Only the shared transformations and old row constraints can shorten a clipped
receiver word. Its own lookup price contributes once per original group. -/
theorem clipped_rows (v : ResetOutput) (c previous transform next h : ℕ)
    (valid : next≤c) (short : 8*v.groupWidth≤h) :
    chunks (2^c) (2^(v.exponent previous transform next h))*h≤
      (2^(c-previous)+2^(c-transform)+2^(c-next))*h+16*2^c*v.groupWidth := by
  let a:=min previous (min transform next)
  let e:=v.exponent previous transform next h
  have ac : a≤c := ((Nat.min_le_right ..).trans (Nat.min_le_right ..)).trans valid
  have ea : e≤a := Nat.min_le_left ..
  have ec : e≤c := ea.trans ac
  have tail : (c-a)+(a-e)=c-e := by omega
  have axes : 2^(c-a)*(2^a)=2^c := by rw [←pow_add,Nat.sub_add_cancel ac]
  have scale : 2^(c-a)*(2^(a-e))=2^(c-e) := by rw [←pow_add,tail]
  have paid := v.pitch_price (2^(c-a)) previous transform next h short
  change 2^(c-a)*2^(a-e)*h≤2^(c-a)*h+16*2^(c-a)*2^a*v.groupWidth at paid
  rw [scale,show 16*2^(c-a)*2^a=16*(2^(c-a)*2^a) by ring,axes] at paid
  have pick : a=previous ∨ a=transform ∨ a=next := by
    dsimp [a]
    omega
  have overhead : 2^(c-a)≤2^(c-previous)+2^(c-transform)+2^(c-next) := by
    rcases pick with hp | ht | hn
    · rw [hp]
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    · rw [ht]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    · rw [hn]
      exact Nat.le_add_left _ _
  rw [dyadic_chunks _ _ ec]
  exact paid.trans (Nat.add_le_add_right (Nat.mul_le_mul_right h overhead) _)

theorem root_lookup_operand (v : ResetOutput) (previous transform next h : ℕ)
    (short : 8*v.groupWidth≤h) :
    let m:=v.middle
    let a:=DescentFallbackPeriod.Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth)
      v.front.donor.cap m.rotorBits m.rootDepth
    (m.rootField*(a+1))*2^(v.exponent previous transform next h)≤h/2 := by
  dsimp only
  apply v.operand_room previous transform next h short
  left
  simp [rootUnits]

/-- At a boundary the predecessor venue has already adopted the upcoming
Walsh cut. This eliminates the prior-width term in the complete row price. -/
theorem boundary_rows (v : ResetOutput) (c k h b : ℕ) (pos : 0<b) (localRoom : 8*b≤h)
    (rootRoom : 8*v.groupWidth≤h) :
    let cut:=laneBits (c+k) h b-k
    chunks (2^c) (2^(v.exponent cut cut (c-k) h))*h≤
      (2+2^k)*h+2^c*(32*2^k*b+16*v.groupWidth) := by
  let l:=laneBits (c+k) h b
  let cut:=l-k
  have bill:=v.clipped_rows c cut cut (c-k) h (Nat.sub_le ..) rootRoom
  have low : l≤c+k := Nat.min_le_left ..
  have axes : c-cut≤c+k-l := by dsimp [cut];omega
  have layer:=per_layer (m:=c+k) 1 pos localRoom
  have walsh : 2^(c-cut)*h≤h+16*(2^c*2^k)*b := by
    apply (Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by decide : 0<2) axes)).trans
    simpa [l,pow_add] using layer
  have other := Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by decide : 0<2)
    (show c-(c-k)≤k by omega))
  change chunks (2^c) (2^(v.exponent cut cut (c-k) h))*h≤_
  apply bill.trans
  nlinarith only [walsh,other]

/-- A programmed reset is precisely one radix below its predecessor. -/
theorem next_difference (S : DescentCompiler.AtomSchedule) (k tail i : ℕ) (live : i<S.length) :
    S.groupWidth k tail i=S.groupWidth k tail (i+1)+k := by
  unfold DescentCompiler.AtomSchedule.groupWidth
  have d : S.length-i=(S.length-(i+1))+1 := by omega
  rw [d,Nat.mul_succ]
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
