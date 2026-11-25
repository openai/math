import OAI.Hierarchy.DescentOrdinaryShapeSlots
import OAI.Hierarchy.DescentIncomingHosts
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The physical compact root labels fit the next calendar host bank -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
noncomputable section

theorem round_slots {t j : ℕ} (reset : ℕ) (stage : j<t) :
    4*DescentOrdinaryVenueReturn.shapeSlots (atRound j)≤2^hostRate t reset :=by
  let n:=DescentOrdinaryVenueReturn.shapeSlots (atRound j)
  have term : 2*n≤hostRate t reset:=by
    have part:2*n≤∑i : Fin t,2*(2^packExponent 20 (atRound i.val)+2):=
      Finset.single_le_sum (f:=fun i:Fin t=>2*(2^packExponent 20 (atRound i.val)+2))
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨j,stage⟩:Fin t))
    exact part.trans (Nat.le_add_left ..)
  have two : 2≤n:=Nat.le_add_left ..
  have lower : 4*n≤2*n^2+1:=by nlinarith only [Nat.mul_le_mul_right n two]
  exact lower.trans ((Nat.two_mul_sq_add_one_le_two_pow_two_mul n).trans (Nat.pow_le_pow_right (by decide) term))

theorem compact_host_room (S : AtomSchedule) {i k D : ℕ}
    (live : 0<S.hostSize i) (active : i+1≤S.length)
    (radix : S.radix=2^k) (slots : 4*DescentOrdinaryVenueReturn.shapeSlots D≤2^S.hostGain) :
    hostRows (S.hostSize i)*((2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots D)≤NativePitch.incomingHosts S (i+1) :=by
  have wide := Nat.sub_le (2^(k+1)) 1
  have bound:=Nat.mul_le_mul (hostRows_double live) (Nat.mul_le_mul_right (DescentOrdinaryVenueReturn.shapeSlots D) wide)
  apply bound.trans
  apply le_trans _ (NativePitch.hosts_bounds S (i+1) active).1
  have step : S.hostSize (i+1)=S.hostSize i*(2^S.hostGain*2^k):=by
    unfold AtomSchedule.hostSize;rw [pow_succ _ i,radix];ring
  rw [step,pow_succ 2 k]
  calc
    _ = S.hostSize i*((4*DescentOrdinaryVenueReturn.shapeSlots D)*2^k):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ slots)

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
