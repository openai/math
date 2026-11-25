import OAI.Computability.BorderVNP.CubeTeamRowClock
import OAI.Computability.BorderVNP.CubeISAOwnedScatterRow
import OAI.Computability.BorderVNP.CubeISAOwnedScatterSingleRow

/-! # Team clock for the actual native packet and singleton scatter loops -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical Physical.Owned Finset

variable {n d : ℕ}

/-- Exact packet-row tick allowance from `PacketRowData.scatterRow_run`. -/
def packetTicks (n d blocks b h K s : ℕ) :=
  (∑ t : Fin (packetTrials n d blocks), (6*n+22 +
    if packetTrialValid t then Scatter.ownedPacketCost n b h K s else 1)) + 1

/-- Exact ordered singleton-row tick allowance from `SingleRowData.scatterRow_run`. -/
def singleTicks (blocks width : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  (∑ t : Fin (singlePairTrials n d), (6*n+20 + if singleTrialValid i u v t then
    Scatter.startSingle.slots+5*(blocks*width)+2 else 1)) + 1

/-- One owned role in an unordered row. A strict row scatters its packet
sides and both orientations of its singleton intervals. -/
def scatterRoleTicks (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  if u = v then singleTicks blocks (h*b) i u v else
    packetTicks n d blocks b h K s + singleTicks blocks (h*b) i u v + singleTicks blocks (h*b) i v u

/-- Coefficient on the fixed-cost trial preparation in an owned row. -/
def scatterProbe (n : ℕ) := 2*(6*n+22+Scatter.startSingle.slots)+3

/-- Work factor for a raw packet wire or an actual singleton bit. -/
def scatterBit (n b h K s : ℕ) := max (4^n*(6*n+23+Scatter.ownedPacketCost n b h K s)) 5

private theorem packetCount_strict (blocks : ℕ) (i : Fin (n+1)) (sym : Symbols d) :
    packetCount blocks i sym.val.1 sym.val.2 =
      Fintype.card {p : Packet n d blocks // p.1.1 i = sym} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun _ => packet_itemRow_eq_iff (width := 0) i sym _)

/-- Padded candidate work in a strict packet row is proportional to its physical packet count. -/
theorem packetTicks_le (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) (hne : u ≠ v) :
    packetTicks n d blocks b h K s ≤
      scatterBit n b h K s * packetCount blocks i u v + 1 := by
  let C := 6*n+23+Scatter.ownedPacketCost n b h K s
  have count : packetTrials n d blocks ≤ 4^n * packetCount blocks i u v := by
    rcases lt_or_gt_of_ne hne with huv | hvu
    · let sym : Symbols d := ⟨(u,v),huv⟩
      rw [packetCount_strict blocks i sym]
      exact packetTrials_le_four_pow_card i sym
    · let sym : Symbols d := ⟨(v,u),hvu⟩
      have swap : packetCount blocks i u v = packetCount blocks i v u := by
        unfold packetCount
        rw [show Sym2.mk u v = Sym2.mk v u from Sym2.eq_swap]
      rw [swap,packetCount_strict blocks i sym]
      exact packetTrials_le_four_pow_card i sym
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ : Fin (packetTrials n d blocks), C := sum_le_sum fun t _ => by dsimp [C]; split <;> omega
    _ = packetTrials n d blocks*C := by simp
    _ ≤ (4^n*packetCount blocks i u v)*C := Nat.mul_le_mul_right _ count
    _ = (4^n*C)*packetCount blocks i u v := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left ..)

private def singleProbe (n : ℕ) := 6*n+22+Scatter.startSingle.slots

/-- Only the valid ordered singleton families consume any per-bit ticks. -/
theorem singleTicks_le_trials (blocks width : ℕ) (i : Fin (n+1)) (u v : Fin d) :
    singleTicks blocks width i u v ≤ (6*n+22+Scatter.startSingle.slots)*(d^n)^2 +
      5*Fintype.card (SingleScan blocks width i u v) + 1 := by
  let good := singleTrialValid i u v
  have bits : (∑ t : Fin (singlePairTrials n d), if good t then 5*(blocks*width) else 0) =
      5*Fintype.card (SingleScan blocks width i u v) := by
    rw [← sum_filter, Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,good]
    ring
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ t : Fin (singlePairTrials n d), (singleProbe n + if good t then 5*(blocks*width) else 0) :=
      sum_le_sum fun t _ => by
        by_cases h : good t <;> simp [singleProbe,show good t = singleTrialValid i u v t from rfl] at h ⊢ <;> simp [h] <;> omega
    _ = singleProbe n * singlePairTrials n d + 5*Fintype.card (SingleScan blocks width i u v) := by
      rw [sum_add_distrib,bits]; simp [Nat.mul_comm]
    _ = _ := by rw [pow_two]; rfl

/-- Concrete row callbacks used by the scatter code satisfy the generic physical-row budget. -/
theorem scatterRoleTicks_le_trials (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) (positive : 0 < h*b) :
    scatterRoleTicks blocks b h K s i u v ≤
      scatterProbe n*(d^n)^2 + scatterBit n b h K s*rowRaw blocks (h*b) i u v := by
  let Z := (d^n)^2
  let C := scatterBit n b h K s
  let B := singleProbe n
  have zpos : 1 ≤ Z := pow_pos (pow_pos (Nat.zero_lt_of_lt u.isLt) _) _
  have cb : 5 ≤ C := le_max_right ..
  have pw : 0 < 2^n*(h*b) := Nat.mul_pos (pow_pos (by decide) _) positive
  let count := packetCount blocks i u v
  have wire := Nat.le_mul_of_pos_right count pw
  have cover := Nat.mul_le_mul_left C wire
  have probeEq : scatterProbe n*Z = 2*(B*Z)+3*Z := by dsimp [scatterProbe,B,singleProbe]; ring
  have h1 := singleTicks_le_trials blocks (h*b) i u v
  change singleTicks blocks (h*b) i u v ≤ B*Z+5*Fintype.card (SingleScan blocks (h*b) i u v)+1 at h1
  by_cases diag : u = v
  · subst v
    have hd : Fintype.card (SingleScan blocks (h*b) i u u) = singleCount blocks (h*b) i u u :=
      Fintype.card_congr (singleDiagRowEquiv blocks (h*b) i u)
    rw [hd] at h1
    have bits := Nat.mul_le_mul_right (singleCount blocks (h*b) i u u) cb
    simp only [scatterRoleTicks,ite_true,rowRaw,Nat.mul_add]
    change _ ≤ scatterProbe n*Z + (C*(_*_) + C*_)
    rw [probeEq]
    omega
  · have h2 := singleTicks_le_trials blocks (h*b) i v u
    change singleTicks blocks (h*b) i v u ≤ B*Z+5*Fintype.card (SingleScan blocks (h*b) i v u)+1 at h2
    have hc : Fintype.card (SingleScan blocks (h*b) i u v) + Fintype.card (SingleScan blocks (h*b) i v u) =
        singleCount blocks (h*b) i u v := by
      rw [← Fintype.card_sum]
      exact Fintype.card_congr (singleStrictRowEquiv blocks (h*b) i u v diag)
    have bits : 5*Fintype.card (SingleScan blocks (h*b) i u v) + 5*Fintype.card (SingleScan blocks (h*b) i v u) ≤
        C*singleCount blocks (h*b) i u v := by
      rw [← Nat.mul_add,hc]
      exact Nat.mul_le_mul_right _ cb
    have pack := packetTicks_le blocks b h K s i u v diag
    change packetTicks n d blocks b h K s ≤ C*count+1 at pack
    simp only [scatterRoleTicks,diag,ite_false,rowRaw,Nat.mul_add]
    change _ ≤ scatterProbe n*Z + (C*(count*_) + C*_)
    rw [probeEq]
    omega

/-- The full-label preparation bound follows from the smaller exact two-tail bound. -/
theorem scatterRoleTicks_le (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) (positive : 0 < h*b) :
    scatterRoleTicks blocks b h K s i u v ≤
      scatterProbe n*(d^(n+1))^2 + scatterBit n b h K s*rowRaw blocks (h*b) i u v := by
  have hd : d^n ≤ d^(n+1) := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt u.isLt)
  exact (scatterRoleTicks_le_trials blocks b h K s i u v positive).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2)) _)

/-- The exact owned-role scatter work of a native team is within the paper's local clock. -/
theorem scatterTeamClock_le_exterior {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (X overhead s : ℕ) (positive : 0 < h*b)
    (cap : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    teamClock (fun u : Fin l.groups => mem (teams.owners+u.val)) team.val overhead (scatterRoleTicks blocks b h K s D.1) ≤
      (overhead+scatterProbe n)*(l.groups^(n+1))^4 + scatterBit n b h K s*(1000000*X/256) :=
  teamClock_le_exterior result image team X overhead _ _ _ (fun u v => scatterRoleTicks_le _ _ _ _ _ _ u v positive) cap

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
