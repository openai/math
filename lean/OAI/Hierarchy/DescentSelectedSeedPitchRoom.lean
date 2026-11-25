import OAI.Hierarchy.DescentSeedPreviousPitch
import OAI.Hierarchy.DescentDatePortArchivePitchRoom

namespace OAI
/-! # The two packed buses of the selected initial physical register -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSixParty.Chronology Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)

/-- Choose the pitch rate and threshold before the number of sites, addresses and the genuine
seed approximation. The grain is the original split announced by the chosen public schedule. -/
theorem selected_seed_pitch_room (t f g reset drift degreeMax quota : ℕ) :
    ∃C : ℕ,∃B₀ : ℕ→ℕ,∀τ B,0<τ → B₀ τ≤B →
      ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀M degree base field wire hist : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let sockets:=2^Nat.clog 2 (NativeBranch.localLimit G S)
        let split:=NativeBranch.binLimit (k:=k) S
        let q:=sockets*(G.b^(t*J)*G.b)
        let p:=split*(h/(16*(q*split)))
        let l:=selectedLayout G S h k (tail τ J) g p drift degree f quota base field wire hist
        ∀cp nP (X : Catalyst.Approximation F cp nP) (R H : ℕ),degree≤degreeMax →
          (DatePorts.initial G op X R l k H (S.groupCount 0) h (S.grainAt G.b p 0)).ArchivePitchRoom
            (S.groupCount 0) h (scale J C) (scale J C) := by
  obtain ⟨C,B₀,pitches⟩:=previous_pitches G op t f g reset drift degreeMax quota
  refine ⟨C,B₀,?_⟩
  intro τ B positive paid
  filter_upwards [pitches τ B positive paid,eventually_ge_atTop 1] with h rooms large
  dsimp only
  intro M degree base field wire hist cp nP X R H small
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let sockets:=2^Nat.clog 2 (NativeBranch.localLimit G S)
  let split:=NativeBranch.binLimit (k:=k) S
  let p:=split*(h/(16*((sockets*(G.b^(t*J)*G.b))*split)))
  let l:=selectedLayout G S h k (tail τ J) g p drift degree f quota base field wire hist
  obtain ⟨operand,role⟩:=rooms M degree base field wire hist small
  have density:=DatePorts.initial_density G op X R l k H (S.groupCount 0) h (S.grainAt G.b p 0)
    (scale J C) (scale J C) operand role
  have shape:=DatePorts.initial_widths (p:=p) G S op X R h k (tail τ J) g drift degree f quota base field wire hist H (S.groupCount 0)
  have positiveGroups : 0<S.groupCount 0 := by
    change 0 < 2^(tail τ J)*(2^k)^(S.length-0)
    positivity
  exact density.pitch_room shape large positiveGroups

end
end Hierarchy.DescentDatedSeedStartup

end OAI
