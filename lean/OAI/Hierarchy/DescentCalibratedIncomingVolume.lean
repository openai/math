import OAI.Hierarchy.DescentIncomingWalshWidth
import OAI.Hierarchy.DescentIncomingPitchDensity
import OAI.Hierarchy.DescentAllDateDonorWidth
import OAI.Hierarchy.DescentSeedOriginScales

namespace OAI
/-! # Cofinal volume of the complete incoming packed stage on the genuine public calendar -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Stage.Dated DescentResetGates DescentPrimitivePalette
open DescentDatedSeedStartup DescentSIMDLookup Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)

/-- There is one packing exponent selected before the tail multiplier and the machine
word. The calendar may choose its remaining ordinary compiler fields independently. -/
theorem dated_volume (t f g reset:ℕ):
    ∃e:ℕ,∀(_op:RotorSpec)(_drift τ B:ℕ),e+2≤B→G.b≤2^(capRate G t g)→
      2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B→
      ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀copies p i H:ℕ,let S:=stageNumbers G t J f g reset copies (tail τ J)
          let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
          ∀ordinary:ℕ→Ordinary,p≤h→
            (∀j<S.length,j%(S.rounds+1)≠S.rounds→
              (ordinary j).payload=h ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount)→
            let M:=incoming S k (tail τ J) p f h ordinary i
            0<M ∧ M≤h/2 ∧ H*chunks (S.groupCount i) M*h≤H*h+H*S.groupCount i*scale J e:=by
  obtain ⟨a,original⟩:=all_donor_rate G t f g reset
  let κ:=groupRate G t f g reset
  let e:=max (2+a) (4+κ+3)
  refine ⟨e,?_⟩;intro _op _drift τ B room branch finalRoom
  have positive:0<B:=by omega
  filter_upwards [walsh_rate G t f g reset τ B positive, terminal_half G _op _drift t f g reset τ B branch positive finalRoom,
    eventually_late 1 B positive, eventually_ge_atTop 1] with h wal terminal old word
  intro J copies p i H S k ordinary input stages
  have lift {x y:ℕ}(xy:x≤y):scale J x≤ scale J y:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ xy)
  have limit : 4 * scale J e ≤ h := epoch_room h B e (by omega) room old
  apply incoming_rows S k (tail τ J) p f h ordinary H i (scale J e) rfl rfl
  · intro live away
    have src:=stages i live away
    obtain ⟨nz,amount⟩:=original J copies (tail τ J) p i
    refine ⟨src.1,src.2.symm ▸ nz,?_,?_⟩
    · have v:(ordinary i).unit≤ scale J e:=src.2 ▸ amount.trans (lift (by dsimp only [e];omega))
      omega
    · rw [src.2]
      calc
        _ ≤ scale J 2*scale J a:=Nat.mul_le_mul (by change 2^2≤2^(2*(J+1));apply Nat.pow_le_pow_right (by decide);omega) amount
        _ ≤ scale J e:=(scale_mul ..).le.trans (lift (le_max_left ..))
  · intro live boundary
    have depth:2^k≤ scale J κ:=Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
    obtain ⟨small,bits⟩:=wal copies p i input live.le
    refine ⟨small,?_⟩
    calc
      _ ≤ scale J 4*scale J κ*scale J 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul (by change 2^4≤2^(4*(J+1));apply Nat.pow_le_pow_right (by decide);omega) depth) bits
      _ ≤ scale J e:=by rw [scale_mul,scale_mul];exact lift (le_max_right ..)
  · intro _;exact terminal copies p input

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
