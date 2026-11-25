import OAI.Hierarchy.DescentTerminalWidthRowLast
import OAI.Hierarchy.ProtocolRAMIndexedWrite

namespace OAI
/-! # One sparse correction per group in the concatenated padded profile column -/
namespace Hierarchy.DescentTerminalWidthRowsRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMIndexedWrite DescentTerminalDenseHeader DescentTerminalHeaderGroups
open ThreeFlat.Routing
open scoped Fin.CommRing
noncomputable section
variable {w groups R : ℕ} (q p : ℕ) (c : Fin groups → ℕ) (out sink : ℕ)
def target (i : Fin groups) := if poolBatchCount (c i) q=0 then sink
  else out+((passed q p c (i.val+1)).length-1)
def patch (i : Fin groups) : Word w := tailCode q p (c i)

theorem target_range (room : (tape q p c).length≤R) (right : out+R≤ sink) (i : Fin groups) :
    out≤target q p c out sink i ∧ target q p c out sink i≤ sink := by
  have h := within q p c (i.val+1)
  unfold target
  split <;> omega

theorem scattered (m : Memory w) (_room : (tape q p c).length≤R) (right : out+R≤ sink)
    (cleared : ∀j:Fin R,m (out+j.val)=(value q p c 0 j.val:Word w)) (r : Fin R) :
    ProtocolRAMIndexedWrite.image (target q p c out sink) (patch (w:=w) q p c) m groups (out+r.val)=
      ((encode q p (padded (tape q p c) r)).val:Word w) := by
  have step (k : ℕ) (hk : k≤groups) :
      ProtocolRAMIndexedWrite.image (target q p c out sink) (patch (w:=w) q p c) m k (out+r.val)=
        (value q p c k r.val:Word w) := by
    induction k with
    | zero => exact cleared r
    | succ k ih =>
      have live : k<groups := by omega
      let i : Fin groups := ⟨k,live⟩
      have previous := ih (Nat.le_of_lt live)
      have ends := passed_len q p c i
      have pos := r.isLt
      have eqn : out+r.val=target q p c out sink i ↔
          poolBatchCount (c i) q≠0 ∧ r.val+1=(passed q p c (i.val+1)).length := by
        unfold target
        split <;> omega
      rw [ProtocolRAMIndexedWrite.image, dite_eq_left live, update q p c i r.val]
      by_cases same : out+r.val=target q p c out sink i
      · rw [ite_eq_left (eqn.mp same), same]
        exact Function.update_self (target q p c out sink i) (patch (w:=w) q p c i)
          (ProtocolRAMIndexedWrite.image (target q p c out sink) (patch (w:=w) q p c) m k)
      · rw [ite_eq_right (fun h=>same (eqn.mpr h)),Function.update_of_ne same]
        exact previous
  simpa only [finish q p c r] using step groups le_rfl


end
end Hierarchy.DescentTerminalWidthRowsRAM

end OAI
