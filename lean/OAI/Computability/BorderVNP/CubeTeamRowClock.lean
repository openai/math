import OAI.Computability.BorderVNP.CubeGroupNativeRoom
import OAI.Computability.BorderVNP.CubeISAOwnedScanBudget
import OAI.Computability.BorderVNP.CubeTeamBudgetFrame

/-! # Clock of the owned group-row traversal

A team tests all ordered symbol pairs. Each owned first symbol selects its
role in the unordered row; a team owning both distinct symbols has two roles.
Packets and singleton bits charge their original padded widths to that first
symbol. Its weight in the public assignment therefore bounds the local work.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical Physical.Owned Finset

variable {n d : ℕ}

/-- Number of physical packets in an unordered symbol row. -/
def packetCount (blocks : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  Fintype.card {p : Packet n d blocks // itemRow i (.inl p : Item n d blocks 0) = Sym2.mk u v}

/-- Number of singleton bits in an unordered row, counting all actual orientations. -/
def singleCount (blocks width : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  Fintype.card {z : SingleSlot n d blocks width // itemRow i (.inr z) = Sym2.mk u v}

/-- Raw packet wires and singleton bits processed in this role. -/
def rowRaw (blocks width : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  packetCount blocks i u v*(2^n*width) + singleCount blocks width i u v

private theorem fiber_charge {T : Type*} [Fintype T] (row : T → Sym2 (Fin d))
    (u : Fin d) (width : ℕ) :
    (∑ v : Fin d, Fintype.card {z : T // row z = Sym2.mk u v}*width) =
      ∑ z : T, if u ∈ row z then width else 0 := by
  classical
  have per (v : Fin d) :
      Fintype.card {z : T // row z = Sym2.mk u v}*width =
        ∑ z : T, if row z = Sym2.mk u v then width else 0 := by
    rw [← sum_filter, Fintype.card_subtype]
    simp
  simp_rw [per]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  by_cases hit : u ∈ row z
  · obtain ⟨t,ht⟩ := Sym2.mem_iff_exists.mp hit
    have he (v : Fin d) : row z = Sym2.mk u v ↔ t = v := ht ▸ (Sym2.mkEmbedding u).injective.eq_iff
    simp [he,hit]
  · have miss (v : Fin d) : row z ≠ Sym2.mk u v := fun h => hit (Sym2.mem_iff_exists.mpr ⟨v,h⟩)
    simp [miss,hit]

/-- Summing over partners counts each physical item once for this endpoint
symbol, even when both endpoints of a singleton have the same symbol. -/
theorem sum_rowRaw (blocks width : ℕ) (i : Fin (n+1)) (u : Fin d) :
    (∑ v, rowRaw blocks width i u v) = groupRaw (blocks*width) i u := by
  simp only [rowRaw,packetCount,singleCount,sum_add_distrib]
  rw [fiber_charge (fun p : Packet n d blocks => itemRow i (.inl p : Item n d blocks 0))]
  have hs := fiber_charge (fun z : SingleSlot n d blocks width => itemRow i (.inr z)) u 1
  simp only [mul_one] at hs
  rw [hs]
  rw [← item_raw_eq_groupRaw (blocks := blocks) (width := width) i u]
  apply congrArg₂ Nat.add
  all_goals
    apply sum_congr rfl
    intro z _
    simp only [itemRow]
  all_goals split_ifs <;> rfl

/-- Total raw volume assigned to the given team. -/
def ownedRaw (owner : Fin d → ℕ) (team S : ℕ) (i : Fin (n+1)) :=
  ∑ u : Fin d, if owner u = team then groupRaw S i u else 0

/-- Actual ordered outer-loop clock with a fixed per-position owner test.
The accepted callback receives the owned endpoint first. -/
def teamClock (owner : Fin d → ℕ) (team overhead : ℕ) (cost : Fin d → Fin d → ℕ) :=
  ∑ u : Fin d, ∑ v : Fin d, (overhead + if owner u = team then cost u v else 0)

/-- Sum a fixed candidate allowance over the actual square traversal. Only the
owned first symbols contribute a term for their raw wires. -/
theorem teamClock_le_rows (blocks width : ℕ) (i : Fin (n+1)) (owner : Fin d → ℕ)
    (team overhead rowProbe bit : ℕ) (cost : Fin d → Fin d → ℕ)
    (row : ∀ u v, cost u v ≤ rowProbe + bit*rowRaw blocks width i u v) :
    teamClock owner team overhead cost ≤ d*d*(overhead+rowProbe) + bit*ownedRaw owner team (blocks*width) i := by
  have localBound (u : Fin d) :
      (∑ v, (overhead + if owner u = team then cost u v else 0)) ≤
        d*(overhead+rowProbe) + bit*(if owner u = team then groupRaw (blocks*width) i u else 0) := by
    by_cases owned : owner u = team
    · simp only [owned,ite_true]
      calc
        _ ≤ ∑ v : Fin d, ((overhead+rowProbe) + bit*rowRaw blocks width i u v) :=
          sum_le_sum fun v _ => by have := row u v; omega
        _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_rowRaw]; simp
    · simp [owned,Nat.mul_add]
  calc
    _ ≤ ∑ u : Fin d, (d*(overhead+rowProbe) + bit*(if owner u = team then groupRaw (blocks*width) i u else 0)) :=
      sum_le_sum fun u _ => localBound u
    _ = _ := by
      rw [sum_add_distrib]
      simp only [ownedRaw,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Finset.mul_sum]
      ring

/-- Aggregate bound for the filtered traversal, with per-row candidate preparation
and variable work charged only to the raw volume of the symbols the team owns. -/
theorem teamClock_le (blocks width : ℕ) (i : Fin (n+1)) (owner : Fin d → ℕ)
    (team overhead probe bit : ℕ) (cost : Fin d → Fin d → ℕ)
    (row : ∀ u v, cost u v ≤ probe*(d^(n+1))^2 + bit*rowRaw blocks width i u v) :
    teamClock owner team overhead cost ≤
      (overhead+probe)*(d^(n+1))^4 + bit*ownedRaw owner team (blocks*width) i := by
  let Z := d^(n+1)
  have hd : d ≤ Z := Nat.le_self_pow (Nat.succ_ne_zero _) _
  have hsq : d*d ≤ Z^2 := by simpa only [pow_two] using Nat.mul_le_mul hd hd
  have h4 : d*d ≤ Z^4 := hsq.trans (by
    rw [show Z^4 = (Z^2)^2 by ring]
    exact Nat.le_self_pow (by decide) _)
  apply (teamClock_le_rows blocks width i owner team overhead _ bit cost row).trans
  apply Nat.add_le_add_right
  have b1 := Nat.mul_le_mul_right overhead h4
  have b2 := Nat.mul_le_mul_right probe (Nat.mul_le_mul_right (Z^2) hsq)
  rw [show Z^2*Z^2 = Z^4 by ring] at b2
  change d*d*(overhead+probe*Z^2) ≤ (overhead+probe)*Z^4
  rw [Nat.mul_add,show d*d*(probe*Z^2) = d*d*Z^2*probe by ring,
    Nat.add_mul,Nat.mul_comm overhead,Nat.mul_comm probe]
  exact Nat.add_le_add b1 b2

/-- Each ordered symbol position fixes one coordinate of each endpoint label.
Its two tails have only `d^(2n)` candidates, so the total candidate volume is exactly `Z²`. -/
theorem teamClock_le_sq (blocks width : ℕ) (i : Fin (n+1)) (owner : Fin d → ℕ)
    (team overhead probe bit : ℕ) (cost : Fin d → Fin d → ℕ)
    (row : ∀ u v, cost u v ≤ probe*(d^n)^2 + bit*rowRaw blocks width i u v) :
    teamClock owner team overhead cost ≤
      (overhead+probe)*(d^(n+1))^2 + bit*ownedRaw owner team (blocks*width) i := by
  apply (teamClock_le_rows blocks width i owner team overhead _ bit cost row).trans
  apply Nat.add_le_add_right
  have hd : d ≤ d^(n+1) := Nat.le_self_pow (Nat.succ_ne_zero _) _
  have eq : d*d*(probe*(d^n)^2) = probe*(d^(n+1))^2 := by rw [pow_succ]; ring
  rw [Nat.mul_add,eq,Nat.add_mul]
  apply Nat.add_le_add_right
  rw [Nat.mul_comm overhead,pow_two]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hd hd)

private theorem loads_owned (r : ℕ) (ws : ℕ → ℕ) (k : ℕ) (j : Fin (r+1)) :
    TeamNative.loads r ws k j =
      ∑ i ∈ range k, if TeamNative.owner r ws i = j then ws i else 0 := by
  induction k with
  | zero => simp [TeamNative.loads]
  | succ k ih =>
    rw [sum_range_succ]
    by_cases hit : TeamNative.owner r ws k = j
    · subst j
      simp only [TeamNative.owner,TeamNative.loads,Function.update_self,ite_true] at ih ⊢
      rw [ih]
    · have miss : j ≠ firstMinimum (TeamNative.loads r ws k) := Ne.symm hit
      simp [TeamNative.loads,miss,ih,hit]

variable {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
variable {recv : A → Fin l.cells} {w : A → ℕ}

/-- The scaled team word is exactly the sum over its stored owner fiber. -/
theorem stored_team_eq (result : GroupWeights.ScheduleResult l teams orig mem) (team : Fin (teams.r+1)) :
    mem (teams.totals+team.val) =
      ∑ u : Fin l.groups, if mem (teams.owners+u.val) = team.val then mem (l.weights+u.val) else 0 := by
  rw [result.totals, loads_owned, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro u _
  simp only [result.owners u.val u.isLt, result.weights u.val u.isLt, Fin.val_inj]

/-- The scanned raw volume on the actual native owner fiber is bounded by
the stored scaled team weight, which includes one unit for each raw wire. -/
theorem ownedRaw_le_stored (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) :
    ownedRaw (fun u : Fin l.groups => mem (teams.owners+u.val)) team.val (blocks*(h*b)) D.1 ≤ mem (teams.totals+team.val) := by
  rw [stored_team_eq result team]
  apply sum_le_sum
  intro u _
  by_cases hit : mem (teams.owners+u.val) = team.val
  · simp only [hit,ite_true,result.weights u.val u.isLt,image.weight_eq,TeamNative.scaledWeight]
    omega
  · simp only [hit,ite_false,le_refl]

/-- Applying the genuine per-team exterior bound yields a clock controlled
by the fourth power of the label count and by `X₀`. -/
theorem teamClock_le_exterior (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (X overhead probe bit : ℕ) (cost : Fin l.groups → Fin l.groups → ℕ)
    (row : ∀ u v, cost u v ≤ probe*(l.groups^(n+1))^2 + bit*rowRaw blocks (h*b) D.1 u v)
    (cap : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    teamClock (fun u => mem (teams.owners+u.val)) team.val overhead cost ≤
      (overhead+probe)*(l.groups^(n+1))^4 + bit*(1000000*X/256) := by
  have hw := (TeamBudget.Layout.le_teamLimit ⟨teams.r+1,X,teams.totals⟩ _).2 cap
  exact (teamClock_le blocks (h*b) D.1 _ team.val overhead probe bit cost row).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ ((ownedRaw_le_stored result image team).trans hw)) _)

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
