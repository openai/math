import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentOrdinaryRateData

namespace OAI
/-! # Uniform ordinary and reset gains for a fixed menu -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentHostDegree
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem fixed_ordinary_rates (t J f g reset M tail : ℕ) (height : 0<J) :
    let S := stageNumbers G t J f g reset M tail
    let c := cutRate t f g
    let k := groupBits t J S.hostGain S.capGain c
    OrdinaryRates G S k c ∧ reset≤S.hostGain ∧ g≤S.capGain ∧
      f≤c ∧ g≤k ∧ packExponent 20 3≤c ∧ G.b≤2^S.capGain ∧ 3≤S.capGain := by
  let S := stageNumbers G t J f g reset M tail
  let c := cutRate t f g
  let k := groupBits t J S.hostGain S.capGain c
  have hi : ∀(v : Fin t→ℕ) (j : Fin t),v j≤∑i,v i := fun v j=>
    Finset.single_le_sum (f:=v) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have mid : c≤k := by dsimp [k,groupBits];omega
  have start : packExponent 20 3≤c := by dsimp [c,cutRate];omega
  have fc : f≤c := by dsimp [c,cutRate];omega
  have gc : g≤c := by dsimp [c,cutRate];omega
  have ah : reset≤S.hostGain := by change reset≤reset+_;omega
  have ch : g≤S.capGain := by change g≤3+g+G.b+_;omega
  have b : G.b≤S.capGain := by change G.b≤3+g+G.b+_;omega
  have large : 3≤S.capGain := by change 3≤3+g+G.b+_;omega
  refine ⟨⟨height,rfl,rfl,?_,?_,?_,?_,?_⟩,ah,ch,fc,gc.trans mid,start,b.trans Nat.lt_two_pow_self.le,large⟩
  · intro j hj
    have pay := hi (fun i=>2*(2^packExponent 20 (atRound i.val)+2)) ⟨j,hj⟩
    apply le_trans _ Nat.lt_two_pow_self.le
    dsimp only at pay
    change _≤reset+_
    omega
  · intro j hj
    have pay := hi (fun i=>2^gainExponent 20 (atRound i.val)*G.b) ⟨j,hj⟩
    apply le_trans _ Nat.lt_two_pow_self.le
    dsimp only at pay
    change _≤3+g+G.b+_
    omega
  · intro j hj
    have pay := hi (fun i=>2^gainExponent 20 (atRound i.val)*G.b) ⟨j,hj⟩
    apply le_trans _ Nat.lt_two_pow_self.le
    dsimp only at pay
    change _≤3+g+G.b+_-(G.b+3)
    omega
  · intro j hj
    have pay := hi (fun i=>gainExponent 20 (atRound i.val)+packExponent 20 (atRound (i.val+1))) ⟨j,hj⟩
    dsimp only at pay
    dsimp [c,cutRate]
    omega
  · intro j hj
    apply le_trans _ mid
    have pay := hi (fun i=>gainExponent 20 (atRound i.val)+packExponent 20 (atRound (i.val+1))) ⟨j,hj⟩
    dsimp only at pay
    dsimp [c,cutRate]
    omega

end
end Hierarchy.DescentSixParty

end OAI
