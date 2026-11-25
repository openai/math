import OAI.Computability.BorderVNP.TransmissionMultiplicity
import OAI.Computability.BorderVNP.RoutingDemand

/-! # Native cost of copying or checking assigned transmission bits

A team scans every public row once. An interval contributes per-bit work only
when the team is an endpoint. This includes co-located shared intervals whose
bits are guessed once, and co-located data copied directly to their cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Finset

variable {w : ℕ}

/-- The payload work of any active mode costs at most 107 native ticks per
bit, including its cursor and loop guard. -/
theorem Range.teamCost_le_roleBits (r : Range w) (self : Word w) :
    r.teamCost self ≤ 107*(if self = r.teamA ∨ self = r.teamB then r.width.val else 0) := by
  by_cases h : self = r.teamA ∨ self = r.teamB
  · rw [ite_eq_left h]
    unfold Range.teamCost
    cases r.selected self with
    | none => simp
    | some role =>
      cases role with
      | none => simp [payloadCost]
      | some mode =>
        change r.width.val*(mode.bitCode.slots+2) ≤ 107*r.width.val
        rw [Nat.mul_comm 107]
        exact Nat.mul_le_mul_left _ (by cases mode <;> decide)
  · obtain ⟨ha,hb⟩ := not_or.mp h
    simp [Range.teamCost,Range.selected,decision,Decision.role,Range.bank,ha,hb,payloadCost]
    split <;> (try split) <;> rfl

/-- Bit charge on the sending and receiving ends can be bounded by the four
actual counters used in the cube allocation. Co-located intervals are charged
at most twice in the upper bound. -/
theorem sum_teamCost_le {N R : ℕ} (rows : ℕ → Range w) (self : Word w) (u : Fin R)
    (src dst : Fin N → Fin R) (data : Fin N → Bool)
    (ends : ∀ i : Fin N, (self = (rows i).teamA ↔ src i = u) ∧
      (self = (rows i).teamB ↔ dst i = u)) :
    ∑ i ∈ range N, (rows i).teamCost self ≤
      107*(Routing.teamBits src (fun i ↦ (rows i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (rows i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (rows i).width.val) data u +
        Routing.teamBits src (fun i ↦ (rows i).width.val) data u) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Routing.teamBits, ← sum_add_distrib, mul_sum]
  apply sum_le_sum
  intro i _
  apply ((rows i).teamCost_le_roleBits self).trans
  simp only [(ends i).1,(ends i).2]
  apply Nat.mul_le_mul_left
  by_cases ha : src i = u <;> by_cases hb : dst i = u <;> cases data i <;> simp [ha,hb]

/-- With the allocated shared and incoming data widths and the literal-source
budget of §7, the concrete bound for the entire native transmission pass
is linear in the public descriptor count and the exterior budget. -/
theorem eventually_transmitTicks {ξ α : ℝ} (gap : ξ < α/3) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (r N R : ℕ) (rows : ℕ → Range w) (self : Word w) (u : Fin R)
      (src dst : Fin N → Fin R) (data : Fin N → Bool),
      (∀ i : Fin N, (self = (rows i).teamA ↔ src i = u) ∧ (self = (rows i).teamB ↔ dst i = u)) →
      256*(Routing.teamBits src (fun i ↦ (rows i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (rows i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (rows i).width.val) data u) ≤ TeamScales.exterior ξ r n →
      Routing.teamBits src (fun i ↦ (rows i).width.val) data u ≤ 3*r*TeamScales.literal α n →
      setup.slots+(20+decision.depth)*N+(∑ i ∈ range N, (rows i).teamCost self)+1 ≤
        24*(N+1)+TeamScales.exterior ξ r n := by
  filter_upwards [TeamScales.eventually_literals_le gap 768] with n hn
  intro r N R rows self u src dst data ends assigned outgoing
  have large := hn r
  have outer : 256*Routing.teamBits src (fun i ↦ (rows i).width.val) data u ≤
      TeamScales.exterior ξ r n := by
    have h := Nat.mul_le_mul_left 256 outgoing
    have eq : 256*(3*r*TeamScales.literal α n) = 768*r*TeamScales.literal α n := by ring
    exact (h.trans_eq eq).trans large
  have cost := sum_teamCost_le rows self u src dst data ends
  change 19+24*N+(∑ i ∈ range N, (rows i).teamCost self)+1 ≤ _
  omega

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
