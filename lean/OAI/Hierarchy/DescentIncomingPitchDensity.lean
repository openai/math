import OAI.Hierarchy.DescentIncomingPitchNumber
import OAI.Hierarchy.DescentIncomingChunkWork
import OAI.Hierarchy.DescentIncomingPitchBounds

namespace OAI
/-! # Every incoming stage pitch pays one host word and the occupied group digits -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentResetGates DescentPrimitivePalette DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage.Dated DescentDatedSeedStartup Filter
noncomputable section

theorem incoming_rows (S:AtomSchedule)(k tail p f h:ℕ)(ordinary:ℕ→Ordinary)(H i U:ℕ)
    (groups:S.baseGroups=2^tail)(radix:S.radix=2^k)
    (normal:i<S.length→i%(S.rounds+1)≠S.rounds→
      let a:=ordinary i
      a.payload=h ∧ 0<a.unit ∧ 2*a.unit≤h ∧ 4*a.unit≤U)
    (boundary:i<S.length→i%(S.rounds+1)=S.rounds→
      let b:=S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds)
      8*b≤h ∧ 16*2^k*b≤U)
    (endSize:S.length≤ i→0<S.groupCount S.length ∧ S.groupCount S.length≤h/2) :
    let M:=incoming S k tail p f h ordinary i
    0<M ∧ M≤h/2 ∧ H*chunks (S.groupCount i) M*h≤H*h+H*S.groupCount i*U:=by
  dsimp only
  by_cases live:i<S.length
  · by_cases cut:i%(S.rounds+1)=S.rounds
    · rw [incoming,ite_eq_left live,ite_eq_left cut]
      let n:=S.groupWidth k tail i
      let b:=S.localWalshBits p (n+k) f (quota S.rounds)
      obtain ⟨pos,small,full⟩:=reset_density n k h b (Nat.succ_pos _) (boundary live cut).1
      refine ⟨pos,small,chunk_work_or _ _ _ _ _ ?_⟩
      rcases full with all|fill
      · exact Or.inl ((S.group_power groups radix i).symm.le.trans all)
      · exact Or.inr (fill.trans (Nat.mul_le_mul_left _ (boundary live cut).2))
    · rw [incoming,ite_eq_left live,ite_eq_right cut]
      obtain ⟨payload,pos,small,units⟩:=normal live cut
      have dim:(ordinary i).lanesAt=lanes h (ordinary i).unit:=congrArg (fun x=>lanes x (ordinary i).unit) payload
      rw [dim]
      obtain ⟨one,rate⟩:=occupancy h (ordinary i).unit pos small
      refine ⟨one,(Nat.le_mul_of_pos_right _ pos).trans (lanes_fit ..),chunk_work _ _ _ _ _ ?_⟩
      calc
        h ≤4*lanes h (ordinary i).unit*(ordinary i).unit:=rate
        _=lanes h (ordinary i).unit*(4*(ordinary i).unit):=by ring
        _≤_:=Nat.mul_le_mul_left _ units
  · rw [incoming,ite_eq_right live]
    obtain ⟨one,small⟩:=endSize (by omega)
    refine ⟨one,small,chunk_work_or _ _ _ _ _ (Or.inl ?_)⟩
    simp only [AtomSchedule.groupCount,Nat.sub_eq_zero_of_le (by omega : S.length≤ i),Nat.sub_self,le_refl]

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
