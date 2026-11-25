import OAI.Hierarchy.DescentOpenStageCount

namespace OAI
/-! # Exact copy and packing rates on the divisible terminal row quantum -/

namespace Hierarchy.DescentSixParty
open DescentCompiler Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Terminal bins divide every issued grain. Their height may grow with the
chosen residual tail. The source and terminal sockets pay the same row width. -/
theorem stage_open_split_counts (t f g reset τ a d B : ℕ) (pos : 0<B)
    (bought : 2*(a+d)+Nat.clog 2 G.b*(t+1)≤B) :
    let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M q W : ℕ, 0<q → 0<W → q≤2^(a*(J+1)) → W≤2^(d*(J+1)) →
        let S:=stageNumbers G t J f g reset M (τ*(J+1))
        let U:=G.b^(t*J)*G.b
        let p:=W*(h/(16*((q*U)*W)))
        let p₀:=S.firstWidth G.b p
        W∣p ∧ 0<p ∧ q*p₀=(q*U)*p ∧ 16*(q*p₀)≤h ∧ h≤32*(q*p₀) ∧
          0<S.copies*p₀ ∧ Real.logb 2 (S.copies*p₀:ℕ) ≤
            ((τ+κ)*(t+2)+1:ℕ)*(Real.logb 2 (2*(h:ℝ)))^2 := by
  intro κ
  filter_upwards [stage_open_physical_counts G t f g reset τ (a+d) B pos bought,
    eventually_ge_atTop 1] with h clocks large
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M q W live groups size bins
  let S:=stageNumbers G t J f g reset M (τ*(J+1))
  let U:=G.b^(t*J)*G.b
  let piece:=h/(16*((q*W)*U))
  let p:=W*(h/(16*((q*U)*W)))
  have split : p=W*piece := by dsimp only [p,piece];rw [Nat.mul_right_comm q U W]
  have fits : q*W≤2^((a+d)*(J+1)) := by
    rw [Nat.add_mul,pow_add]
    exact Nat.mul_le_mul size bins
  obtain ⟨active,lower,upper,_,_⟩:=clocks M (q*W) (Nat.mul_pos live groups) fits
  have expand (x : ℕ) : S.firstWidth G.b x=x*U := by
    rw [AtomSchedule.firstWidth,S.grain_initial]
    change x*G.b^(t*J)*G.b=x*(G.b^(t*J)*G.b)
    exact Nat.mul_assoc ..
  change 16*((q*W)*S.firstWidth G.b piece)≤h at lower
  change h≤32*((q*W)*S.firstWidth G.b piece) at upper
  have same : q*S.firstWidth G.b p=(q*W)*S.firstWidth G.b piece := by
    rw [expand,expand,split]
    ring
  have positive : 0<p := by rw [split];exact Nat.mul_pos groups active
  have bpos : 0<G.b := by have := G.paid;omega
  have p₀pos : 0<S.firstWidth G.b p := by rw [expand];exact Nat.mul_pos positive (Nat.mul_pos (Nat.pow_pos bpos) bpos)
  have low : 16*(q*S.firstWidth G.b p)≤h := by rw [same];exact lower
  have high : h≤32*(q*S.firstWidth G.b p) := by rw [same];exact upper
  have width : S.firstWidth G.b p≤h := (Nat.le_mul_of_pos_left _ live).trans
    ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans low)
  have age : 2^J≤h := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.div_le_self (Nat.log 2 h) (2*B))).trans (Nat.pow_log_le_self 2 (by omega))
  refine ⟨⟨piece,split⟩,positive,?_,low,high,stage_open_copy_count G t f g reset τ h J M p p₀pos width age⟩
  rw [expand]
  ring

end Hierarchy.DescentSixParty

end OAI
