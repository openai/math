import OAI.Computability.BorderVNP.RoutingISARelayLoops
import OAI.Computability.BorderVNP.RoutingISATableAddressImage

/-!
# Typed meaning and cost of the physical relay checks

The scheduled word loops only visit the increasing half of the endpoint-pair
matrix. They check both copies of every typed hop routed through this team.
The number of occupied iterations is bounded by the exterior demand budget
plus the incomplete rounds for all endpoint pairs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

/-- Either orientation of a pair checks the same Boolean agreement. -/
theorem RelayWordAgrees.swap {pub : Arg → ℕ} {mem : ℕ → ℕ} {u v y q : ℕ}
    (h : RelayWordAgrees pub mem u v y q) : RelayWordAgrees pub mem y v u q :=
  ⟨h.1.symm,h.1 ▸ h.2⟩

/-- The scheduler's increasing endpoint traversal checks exactly the two physical
legs for each hop of the unordered demand list. -/
theorem relayChecks_iff_hops (l : TableLayout) (row : ℕ → TableRow) (hR : 2 < l.teams)
    (v : Fin l.teams) (pub : Arg → ℕ) (mem : ℕ → ℕ) :
    RelayChecks l.teams (fun u j ↦ l.partnerLength row u v j) pub mem v ↔
      ∀ (u : Fin l.teams) (p : Routing.Hop hR (l.widthMatrix row) u v),
        RelayWordAgrees pub mem u v p.1 (p.2.val / (l.teams-2)) := by
  constructor
  · intro checks u p
    have ordered (x : Fin l.teams) (h : Routing.Hop hR (l.widthMatrix row) x v)
        (hx : x < h.1) : RelayWordAgrees pub mem x v h.1 (h.2.val / (l.teams-2)) := by
      apply checks x x.isLt h.1 hx h.1.isLt
      change h.2.val / (l.teams-2) < l.partnerLength row x v h.1
      rw [l.partnerLength_eq row x v h.1, ← Routing.ordinalEquiv_val hR x h.1 v _ h.2]
      exact (Routing.ordinalEquiv hR x h.1 v _ h.2).isLt
    rcases lt_trichotomy u p.1 with hl | he | hg
    · exact ordered u p hl
    · have hp := p.2.property
      simp only [Routing.pairBits, dite_eq_right (not_ne_iff.mpr he), notMem_empty] at hp
    · exact (ordered p.1 (Routing.otherHop hR (l.widthMatrix row) p) hg).swap
  · intro checks x hx y hxy hy q hq
    let u : Fin l.teams := ⟨x,hx⟩
    let j : Fin l.teams := ⟨y,hy⟩
    let e := Routing.ordinalEquiv hR u j v (Routing.demand (l.widthMatrix row) u j)
    let k : Fin (Routing.scheduledLength u j v (Routing.demand (l.widthMatrix row) u j)) :=
      ⟨q,(l.partnerLength_eq row u v j) ▸ hq⟩
    let p := e.symm k
    have eq := Routing.ordinalEquiv_val hR u j v _ p
    change (e (e.symm k)).val = p.val / (l.teams-2) at eq
    rw [e.apply_symm_apply] at eq
    change q = p.val / (l.teams-2) at eq
    rw [eq]
    exact checks u ⟨j,p⟩

/-- At a fixed relay the total number of occupied inner iterations is at most
the exterior budget plus one incomplete round per endpoint pair. -/
theorem relayIterations_le (l : TableLayout) (row : ℕ → TableRow) (hR : 2 < l.teams)
    (v : Fin l.teams) (X : ℕ)
    (budget : ∀ u, ∑ j, Routing.demand (l.widthMatrix row) u j ≤ X / 64) :
    ∑ u ∈ Ico 0 l.teams, ∑ j ∈ Ico (u+1) l.teams, l.partnerLength row u v j ≤ X+l.teams^2 := by
  have one (u : Fin l.teams) :
      ∑ j ∈ Ico (u.val+1) l.teams, l.partnerLength row u v j ≤ X/(64*(l.teams-2))+l.teams := by
    calc
      _ ≤ ∑ j ∈ range l.teams, l.partnerLength row u v j := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact fun j hj ↦ mem_range.mpr (mem_Ico.mp hj).2
        · exact fun _ _ _ ↦ Nat.zero_le _
      _ = Routing.legLoad hR (l.widthMatrix row) u v := l.legPrefix_eq_legLoad row hR u v
      _ ≤ X/(64*(l.teams-2))+l.teams := by
        rw [← Nat.div_div_eq_div_mul]
        exact (Routing.legLoad_le hR _ u v).trans (Nat.add_le_add_right
          (Nat.div_le_div_right (budget u)) _)
  have denom : l.teams ≤ 64*(l.teams-2) := by omega
  have prod : l.teams * (X/(64*(l.teams-2))) ≤ X :=
    (Nat.mul_le_mul_right _ denom).trans (Nat.mul_div_le X _)
  calc
    _ = ∑ u : Fin l.teams, ∑ j ∈ Ico (u.val+1) l.teams, l.partnerLength row u v j := by
      rw [Nat.Ico_zero_eq_range]
      exact (Fin.sum_univ_eq_sum_range (fun u ↦ ∑ j ∈ Ico (u+1) l.teams, l.partnerLength row u v j) _).symm
    _ ≤ ∑ _u : Fin l.teams, (X/(64*(l.teams-2))+l.teams) := sum_le_sum fun u _ ↦ one u
    _ = l.teams * (X/(64*(l.teams-2))) + l.teams^2 := by simp [Nat.mul_add,pow_two]
    _ ≤ X+l.teams^2 := Nat.add_le_add_right prod _

/-- A single team's physical relay scan uses O(X+R²) native ticks, including
all zero-length pair scans and all guard ticks. -/
theorem relayCheckCost_le (l : TableLayout) (row : ℕ → TableRow) (hR : 2 < l.teams)
    (v : Fin l.teams) (X : ℕ)
    (budget : ∀ u, ∑ j, Routing.demand (l.widthMatrix row) u j ≤ X/64) :
    relayCheckCost l.teams (fun u j ↦ l.partnerLength row u v j) ≤
      tableSetup.slots+6+l.teams*4+l.teams^2*(scheduledLengthWord.slots+4)+
        (X+l.teams^2)*(relayBody.slots+1) := by
  let len := fun (u j : ℕ) ↦ l.partnerLength row u v j
  let K := scheduledLengthWord.slots+4
  let B := relayBody.slots+1
  have each (u : ℕ) :
      relayRowCost l.teams len u+1 ≤ 4 + l.teams*K +
        (∑ j ∈ Ico (u+1) l.teams, len u j)*B := by
    have eq (j : ℕ) : relayPairCost (len u j)+1 = K+len u j*B := by
      dsimp [relayPairCost,K,B]; omega
    simp only [relayRowCost,eq,sum_add_distrib,sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_id,←sum_mul]
    have bound := Nat.mul_le_mul_right K (Nat.sub_le l.teams (u+1))
    omega
  have bound := sum_le_sum (s := Ico 0 l.teams) (fun u _ ↦ each u)
  simp only [sum_add_distrib,sum_const,Nat.card_Ico,Nat.sub_zero,nsmul_eq_mul,Nat.cast_id,←sum_mul] at bound
  have prod := Nat.mul_le_mul_right B (relayIterations_le l row hR v X budget)
  unfold relayCheckCost
  change tableSetup.slots+4+1+((∑ u ∈ Ico 0 l.teams, (relayRowCost l.teams len u+1))+1) ≤
    tableSetup.slots+6+l.teams*4+l.teams^2*K+(X+l.teams^2)*B
  rw [pow_two, Nat.mul_assoc]
  change _ ≤ tableSetup.slots+6+l.teams*4+l.teams*(l.teams*K)+(X+l.teams*l.teams)*B
  rw [pow_two] at prod
  change (∑ u ∈ Ico 0 l.teams, ∑ j ∈ Ico (u+1) l.teams, len u j)*B ≤
    (X+l.teams*l.teams)*B at prod
  simp only [sum_add_distrib,sum_const,Nat.card_Ico,Nat.sub_zero,nsmul_eq_mul,Nat.cast_id,mul_one]
  omega

end RoutingISA

end BorderVNP
end Computability
end OAI
