import OAI.Hierarchy.DescentGatheredVectorReshape
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # The operand gather and vector permutation on the two true row shapes -/
namespace Hierarchy.DescentGatheredVectorReshape
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentDatedSeedStartup
noncomputable section

def rowFactor (N Q r nodes source : ℕ) := 1024*(N+1)*(Q+1)*(r+1)*(termBound nodes source+1)

theorem word_bill {N Q D k K cap : ℕ} (C : Fin N→Fin Q→Refs D k K cap)
    (H G J r M a w base out source h ratio u₀ u₁ : ℕ) (src : Bank)
    (limits : ∀p l,let t:=C p l;t.want.work+t.addr.work+t.counts.work≤ source)
    (oldFill : h≤(M*r)*u₀) (newFill : h≤ M*u₁) (lookup : (a*r)*M≤ h/2) (bus : w≤ ratio*h) :
    let nodes:=DescentPackedActorMask.nodes (DescentHaloWalkRAM.breadth D*2^k) K cap
    let factor:=rowFactor N Q r nodes source
    (ticks C H G J r M a src+7*names (program C H G J r M a base out w src))*w ≤
      factor*ratio*(h+2*H*h+H*G*u₀+H*J*u₁)+factor*ratio*2^(h/2)*h :=by
  intro nodes factor
  have regular:=tariff C H G J r M a w base out source src limits
  obtain ⟨clock,text⟩:=regular
  let oldRows:=H*chunks G (M*r)
  let newRows:=H*chunks J M
  let bound:=termBound nodes source
  have pure : 2^((a*r)*M)≤2^(h/2):=Nat.pow_le_pow_right (by decide) lookup
  have shape : DescentVectorBookReshape.rows H Q J r M=r*Q*newRows :=by
    unfold DescentVectorBookReshape.rows newRows
    ring
  have table : DescentVectorBookReshape.dictionaryWords r a M≤ r*2^(h/2) := Nat.mul_le_mul_left _ pure
  have addresses : DescentVectorBookReshape.cells N H Q J r a M≤ r*2^(h/2)+2*(N*(r*Q*newRows)) :=by
    unfold DescentVectorBookReshape.cells
    rw [shape]
    gcongr
  change ticks C H G J r M a src ≤ (4+(N*Q)*(4+oldRows*(2*bound+4)))+
    (8+10*DescentVectorBookReshape.dictionaryWords r a M+74*(N*DescentVectorBookReshape.rows H Q J r M)) at clock
  rw [shape] at clock
  have original : ticks C H G J r M a src+7*names (program C H G J r M a base out w src) ≤
      factor*(1+oldRows+newRows+2^(h/2)) :=by
    calc
      _ ≤ (4+(N*Q)*(4+oldRows*(2*bound+4)))+(8+10*(r*2^(h/2))+74*(N*(r*Q*newRows)))+
        7*((15+(N*Q)*(11+4*bound))+(15*(r*2^(h/2)+2*(N*(r*Q*newRows))+1)+111)) :=by
        refine (Nat.add_le_add clock (Nat.mul_le_mul_left 7 text)).trans ?_
        gcongr
      _ ≤ _ :=by
        change _≤(1024*(N+1)*(Q+1)*(r+1)*(bound+1))*(1+oldRows+newRows+2^(h/2))
        ring_nf
        omega
  have old:=chunk_work H G (M*r) h u₀ oldFill
  have new:=chunk_work H J M h u₁ newFill
  change oldRows*h≤ H*h+H*G*u₀ at old
  change newRows*h≤ H*h+H*J*u₁ at new
  calc
    _ ≤ (factor*(1+oldRows+newRows+2^(h/2)))*(ratio*h) :=Nat.mul_le_mul original bus
    _ = factor*ratio*(h+oldRows*h+newRows*h)+factor*ratio*2^(h/2)*h :=by ring
    _ ≤ factor*ratio*(h+(H*h+H*G*u₀)+(H*h+H*J*u₁))+factor*ratio*2^(h/2)*h :=by gcongr
    _ = _ :=by ring
end
end Hierarchy.DescentGatheredVectorReshape

end OAI
