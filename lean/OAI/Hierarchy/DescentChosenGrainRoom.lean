import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # The genuine socket-aligned initial width fits in the published payload -/
namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

theorem split_first_width (b h bin sockets : ℕ) (live : 0<sockets) :
    let U:=b^(S.rounds*S.height)*b
    let p:=bin*(h/(16*((sockets*U)*bin)))
    S.firstWidth b p≤h :=by
  intro U p
  let N:=16*((sockets*U)*bin)
  have raw:=(Nat.div_mul_le_self h N)
  change _≤h at raw
  rw [firstWidth,S.grain_initial]
  calc
    _ = (h/N)*(bin*U):=by dsimp only [p,N,U];ring
    _ ≤ (h/N)*N:=by
      apply Nat.mul_le_mul_left
      have grow : bin*U≤(sockets*U)*bin:=by
        simpa only [Nat.mul_comm bin U,Nat.mul_assoc] using Nat.mul_le_mul_right bin (Nat.le_mul_of_pos_left U live)
      exact grow.trans (Nat.le_mul_of_pos_left _ (by decide : 0<16))
    _ ≤ h:=raw

theorem grain_le_payload (b p h : ℕ) (base : 0<b) (room : S.firstWidth b p≤h) : p≤h :=by
  rw [firstWidth,S.grain_initial] at room
  exact (Nat.le_mul_of_pos_right p (Nat.pow_pos base)).trans ((Nat.le_mul_of_pos_right _ base).trans room)

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
