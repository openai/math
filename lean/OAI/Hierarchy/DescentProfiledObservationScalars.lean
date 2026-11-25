import OAI.Hierarchy.DescentPublicObservedWordRoom
import OAI.Hierarchy.DescentPrivateClockScale
import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Word width for the ordinary ballot, the selected layout score, and both observed counts -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

variable {F:Type} [Field F]

/-- The batch at the final date counts the unpadded terminal racks and all
frozen groups. Each counted cable is budgeted eight times. -/
theorem observed_batch (S:AtomSchedule) :
    S.batch = S.groupCount S.length*S.hostSize S.length*S.radix*2^(8+S.capGain*S.length)*8 :=by
  simp only [AtomSchedule.batch,AtomSchedule.copies,AtomSchedule.groupCount,AtomSchedule.hostSize,Nat.sub_self,
    pow_zero,mul_one,mul_pow,pow_succ S.radix]
  rw [show 11+S.capGain*S.length=(8+S.capGain*S.length)+3 by omega,pow_add]
  ring

structure ObservationRoom (G:PoweredGadget F) (S:AtomSchedule) (h w:ℕ) : Prop where
  height : 0<S.height
  key : ∀i≤S.length,S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w
  count : ∀i≤S.length,S.groupCount i*hostRows (S.hostSize i)*S.radix*2^(8+S.capGain*i)<2^w
  grain : 2*(DescentTerminalEpochBits.width G.C+1)≤h/2
  score : S.batch*(G.C+8+8*G.k)<2^w

/-- One CPU word factor works for every date and every initial site population
bounded by the input. Its value is chosen before the logarithmic height scale. -/
theorem observation_room_uniform (G:PoweredGadget F) (t f g reset:ℕ) :
    ∃factor:ℕ,∀τ β:ℕ,0<β→∀ᶠ h:ℕ in atTop,
      let J:=Nat.log 2 h/(2*β)
      ∀M:ℕ,M≤(2^h)^2→∀w:ℕ,factor*h≤w→ObservationRoom G (stageNumbers G t J f g reset M (tail τ J)) h w:=by
  obtain ⟨a,capacity⟩:=observed_word_room (G:=G) t f g reset 1
  let b:=8*(G.C+8+8*G.k)
  refine ⟨a+b,?_⟩
  intro τ β positive
  filter_upwards [eventually_ge_atTop (2^(2*β)),eventually_ge_atTop (4*(DescentTerminalEpochBits.width G.C+1)),
    eventually_ge_atTop 1,eventually_ge_atTop (2^(τ*(2*β)))] with h enough grain live reserve
  intro J M initial w room
  let S:=stageNumbers G t J f g reset M (tail τ J)
  have square:(J+1)^2≤h:=private_age_square h β live positive
  have logRoom:2*β≤Nat.log 2 h:=(Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : h≠0)).mpr enough
  have nonzero:0<J:=Nat.div_pos logRoom (by omega)
  have sites:M≤4^h:=by simpa only [←Nat.pow_mul, show (4:ℕ)=2^2 by decide,Nat.mul_comm h 2] using initial
  have grown : τ≤J := (Nat.le_div_iff_mul_le (by omega : 0<2*β)).mpr
    ((Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : h≠0)).mpr reserve)
  have cut : tail τ J≤1*h := by
    rw [one_mul,tail]
    exact (Nat.mul_le_mul_right (J+1) (Nat.le_succ_of_le grown)).trans (by simpa [pow_two] using square)
  have reg:a*h≤w:=(Nat.mul_le_mul_right h (Nat.le_add_right a b)).trans room
  have measured (i:ℕ) (age:i≤S.length):=capacity h J M (tail τ J) i live square sites cut age w reg
  have final_:=(capacity h J M (tail τ J) S.length live square sites cut (le_refl _) (a*h) (le_refl _)).2
  have trueRows:S.groupCount S.length*S.hostSize S.length*S.radix*2^(8+S.capGain*S.length)<2^(a*h):=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hostPad _)))).trans_lt final_
  have bFit:b≤2^(b*h):=by
    refine (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ live))
  refine ⟨nonzero,fun i ok=>(measured i ok).1,fun i ok=>(measured i ok).2,by omega,?_⟩
  rw [observed_batch,mul_assoc _ 8]
  change _*b<2^w
  calc
    _ < 2^(a*h)*b := Nat.mul_lt_mul_of_pos_right trueRows (by dsimp [b];omega)
    _ ≤ 2^(a*h)*2^(b*h) := Nat.mul_le_mul_left _ bFit
    _ ≤ 2^w := by rw [←pow_add,←Nat.add_mul];exact Nat.pow_le_pow_right (by decide) room

theorem observation_room_cofinal (G:PoweredGadget F) (t f g reset τ:ℕ) :
    ∃factor:ℕ,∀β:ℕ,0<β→∀ᶠ h:ℕ in atTop,
      let J:=Nat.log 2 h/(2*β)
      ∀M:ℕ,M≤(2^h)^2→∀w:ℕ,factor*h≤w→ObservationRoom G (stageNumbers G t J f g reset M (tail τ J)) h w:=by
  obtain ⟨factor,ok⟩:=observation_room_uniform G t f g reset
  exact ⟨factor,ok τ⟩

end
end Hierarchy.DescentSixParty

end OAI
