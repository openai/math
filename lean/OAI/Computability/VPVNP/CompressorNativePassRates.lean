import OAI.Computability.VPVNP.CompressorGroupCost
import OAI.Computability.VPVNP.CompressorPassTimeline
import OAI.Computability.VPVNP.CompressorLevelCounts

/-! # Communication rates of the installed pass program

All source calls and probes are charged at their actual multiplicity. The
online controller charges a fixed amount per source call and a fixed recipe
overhead per source packet. The latter is bounded by the number of visits
in the single hardwired block. Neither charge uses the private burst clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BlockPlanner Schedule Compression PassTimeline

/-- Charge per position when the raw source workers use at most `raw`
units per position in the pass. -/
def nativePassRate (A : Script) (raw : ℕ) : ℕ :=
  raw*(arity A.catalog+3) + A.block.length*(Online.Run.maxReads A.plan+4*arity A.catalog+26)

theorem groupCost_nativeRate {w : ℕ} (A : Script) (ps : List (SourceOnline.Packet A w))
    (raw positions : ℕ) (positive : 0 < positions) (visitBound : ps.length ≤ A.block.length)
    (work : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) ≤ raw*positions) :
    groupCost A ps ≤ nativePassRate A raw * positions := by
  let overhead := Online.Run.maxReads A.plan+4*arity A.catalog+26
  have h := Nat.mul_le_mul_right (arity A.catalog+3) work
  have tails : ps.length*overhead ≤ A.block.length*overhead*positions :=
    (Nat.mul_le_mul_right overhead visitBound).trans (Nat.le_mul_of_pos_right _ positive)
  simpa only [groupCost,nativePassRate,Nat.add_mul,Nat.mul_right_comm raw positions] using Nat.add_le_add h tails

/-- Uniform source-rate bound taking the maximum over all shrink indices and the refresh rate. -/
def commonRawRate {s : ℕ} (shrinking : Fin s → ℕ) (refresh : ℕ) :=
  max (Finset.univ.sup shrinking) refresh

/-- Source rate for a particular scheduled pass, selected from the indexed shrink rates or the
single refresh rate. -/
def rawPassRate {s : ℕ} (p : PassTimeline.Pass s) (shrinking : Fin s → ℕ) (refresh : ℕ) :=
  match p with | .shrink i => shrinking i | .refresh => refresh

theorem rawRate_le {s : ℕ} (p : PassTimeline.Pass s) (shrink : Fin s → ℕ) (refresh : ℕ) :
    rawPassRate p shrink refresh ≤ commonRawRate shrink refresh := by
  cases p with
  | shrink i => exact (Finset.le_sup (f := shrink) (Finset.mem_univ i)).trans (le_max_left ..)
  | refresh => exact le_max_right ..

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The full source cost for a shrinking substep or a refresh yields the
same uniform bound for the three physical parts used in the pass runner.
The absolute ordinal equation gives the number of actual worker visits. -/
theorem passCharges_le {a g w : ℕ} (X : State a g) (z : Located S.steps)
    (shrinking : Fin S.steps → ℕ) (refresh positions : ℕ) (hpos : X.positions ≤ positions)
    (pre : List (SourceOnline.Packet (BlockProgram.script B) w)) (selector : SourceOnline.Packet (BlockProgram.script B) w)
    (tail : List (SourceOnline.Packet (BlockProgram.script B) w))
    (len : z.first B + pre.length + 1 + tail.length = z.finish B)
    (raw : RAMBuckets.cost Report.probes ((pre++selector::tail).flatMap SourceWalk.Packet.reports) ≤
      rawPassRate z.pass shrinking refresh * X.positions) :
    groupCost (BlockProgram.script B) pre + groupCost (BlockProgram.script B) [selector] +
      groupCost (BlockProgram.script B) tail ≤ nativePassRate (BlockProgram.script B) (commonRawRate shrinking refresh)*positions := by
  have window := congrArg List.length (z.window B).block
  simp only [List.length_append] at window
  have length : (pre++selector::tail).length ≤ (BlockProgram.script B).block.length := by
    change z.first B+pre.length+1+tail.length = z.first B+(z.visits B).length at len
    simp only [List.length_append,List.length_cons]
    omega
  rw [← groupCost_split_selector]
  exact groupCost_nativeRate _ _ _ _ (X.positions_pos.trans_le hpos) length
    (raw.trans (Nat.mul_le_mul (rawRate_le ..) hpos))

/-- Total of the uniform per-pass bounds in the actual chronological tree,
followed by the calendar's terminal cost of four. -/
theorem timeline_rate (T raw positions : ℕ) :
    (timeline S.steps T).length * (nativePassRate (BlockProgram.script B) raw * positions) + 4 =
      (T*(S.steps+1)) * (nativePassRate (BlockProgram.script B) raw * positions) + 4 := by
  have len : (timeline S.steps T).length = T*(S.steps+1) := by
    induction T with
    | zero => simp [timeline]
    | succ t ih =>
      simp only [timeline,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append] at ih ⊢
      rw [ih,Nat.succ_mul]
      simp [oneBlock]
  rw [len]

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
