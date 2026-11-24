import OAI.Computability.VPVNP.LiveExponentPaths
import OAI.Computability.VPVNP.LiveStagePaths

/-!
# Frame and address guarantees for the linked exponent stage

The public bases are selected so the two input areas precede the carry
array, and all three arrays fit in the RAM address space. The native
program only changes the current label's carry. In particular its
continuing calls preserve the live-program dispatch tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM BurstRAM.PrivateRAM

variable {w t Z : ℕ}

theorem counterAddr_val (pub : Fin 5 → Word w) (a : Fin t) (hfit : (pub 2).val+t ≤ 2^w) :
    (counterAddr pub a).val = (pub 2).val+a.val := by
  have ha := a.isLt
  rw [counterAddr, Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (show a.val < 2^w by omega), Nat.mod_eq_of_lt (by omega)]

private theorem bufferAddress_val (base : Word w) (a : Fin t) (j : Fin Z)
    (fit : base.val+t*Z ≤ 2^w) : (base+posWord a j).val = base.val+(a.val*Z+j.val) := by
  have hj : a.val*Z+j.val < t*Z := calc
    _ < a.val*Z+Z := Nat.add_lt_add_left j.isLt _
    _ = (a.val+1)*Z := (Nat.succ_mul ..).symm
    _ ≤ t*Z := Nat.mul_le_mul_right _ a.isLt
  rw [Fin.val_add]
  change (base.val + ((a.val*Z+j.val) % (2^w))) % (2^w) = _
  rw [Nat.mod_eq_of_lt (show a.val*Z+j.val < 2^w by omega), Nat.mod_eq_of_lt (by omega)]

/-- A numerical memory layout sufficient for the actual digit table.
The two read-only arrays may be separated by other scratch regions. -/
theorem layout_of_ranges (pub : Fin 5 → Word w) (hz : (pub 3).val = Z) (ht : (pub 4).val = t*Z)
    (left : (pub 0).val+t*Z ≤ (pub 2).val) (right : (pub 1).val+t*Z ≤ (pub 2).val)
    (fit : (pub 2).val+t ≤ 2^w) : BufferLayout pub t Z := by
  refine ⟨hz,ht,?_,?_⟩ <;> intro a b j he
  · have h := congrArg Fin.val he
    rw [incomingAddress, bufferAddress_val _ _ _ (left.trans (pub 2).isLt.le), counterAddr_val _ _ fit] at h
    have hi := (finProdFinEquiv (a,j)).isLt
    change j.val+Z*a.val < t*Z at hi
    rw [Nat.mul_comm Z a.val] at hi
    omega
  · have h := congrArg Fin.val he
    rw [outgoingAddress, bufferAddress_val _ _ _ (right.trans (pub 2).isLt.le), counterAddr_val _ _ fit] at h
    have hi := (finProdFinEquiv (a,j)).isLt
    change j.val+Z*a.val < t*Z at hi
    rw [Nat.mul_comm Z a.val] at hi
    omega

/-- Continuing native calls advance the cursor within its range and
preserve any cell outside the entire carry array. -/
theorem frame_result {pub : Fin 5 → Word w} (L : BufferLayout pub t Z)
    {addr : Word w} (fresh : ∀ a : Fin t, counterAddr pub a ≠ addr)
    {s s' : Word w} {m : Memory w} {b : List Bool} {r : Report w} {f : ℕ}
    (hs : s ≤ pub 4)
    (hc : execute (digitTemplate.instantiate w pub).program (f+31)
      ((digitTemplate.instantiate w pub).program.start s) m b = some r)
    (next : r.result = some s') : s' ≤ pub 4 ∧ after m r.events addr.val = m addr.val := by
  rcases lt_or_eq_of_le hs with hlt | rfl
  · obtain ⟨_, rfl⟩ := data_result hlt hc
    obtain rfl : s+1 = s' := Option.some.inj next
    have hv : s.val < t*Z := L.size ▸ hlt
    have hz : 0 < Z := by by_contra! hh; simp [Nat.eq_zero_of_le_zero hh] at hv
    let a : Fin t := ⟨s.val/Z, (Nat.div_lt_iff_lt_mul hz).mpr hv⟩
    have ea : carryAddress pub s = counterAddr pub a := by
      change pub 2 + Fin.ofNat _ (s.val/(pub 3).val) = _
      rw [L.width]
      rfl
    refine ⟨?_,?_⟩
    · change (s+1).val ≤ (pub 4).val
      have hlt' : s.val < (pub 4).val := hlt
      rw [Fin.val_add_one_of_lt' (lt_of_le_of_lt hlt' (pub 4).isLt)]
      exact hlt'
    · rw [digitReport_after, ea, writeMemory, ite_eq_right (fun h => fresh a (Fin.ext h.symm))]
  · rw [show f+31 = (f+26)+5 by omega, execute_done pub (pub 4) m b (f+26) rfl] at hc
    split at hc
    · cases hc
      contradiction
    · contradiction

end LiveExponent

end VPVNP
end Computability
end OAI
