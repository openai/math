import OAI.Hierarchy.ProtocolRAMCalendarSumCalibration
import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # What a mode-one vote proves about the chronological fixed-point score sums -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AttemptGate PurchaseStage
open scoped BigOperators Fin.CommRing
noncomputable section

variable {w q d : ℕ}

/-- Layout of the three scalar tests and mask pass. Every condition is public. -/
structure TestRoom (B : Repair q d) (w : ℕ) : Prop where
  wide : 4≤2^w
  fits : (AttemptGate.mode B.policy).Fits w B.repairBits.base
  stop : B.tests.stop.base<B.tests.excess.out
  excess : B.tests.excess.out+B.tests.excess.rows<B.tests.payload.out
  payload : B.tests.payload.out+B.tests.payload.rows<B.tests.discrepancy.out

private theorem advance_low (injection stop excess payload discrepancy : Bool)
    (mode : selectMode injection false stop excess payload discrepancy=1) :
    excess=false ∧ (injection=true → payload=false) := by
  cases injection <;> cases stop <;> cases excess <;> cases payload <;> cases discrepancy <;>
    simp_all [selectMode]

/-- The four-valued opcode reads three successive genuine score comparisons.
The masking pass can only write above the earlier test expressions. -/
def testResult (B : Repair q d) (m : Memory w) :=
  selectMode B.tests.injection B.tests.reserve (bit B.tests.stop m) (B.tests.excess.high m)
    (B.tests.payload.high (B.tests.excess.after m))
    (B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after m)))

theorem post_result (L : Dispatch) (B : Repair q d) (m : Memory w) (layout : TestRoom B w) :
    actual B.policy (postSnapshot L B m)=testResult B m := by
  let snap := postSnapshot L B m
  have positive : 0<w := by
    by_contra! zero
    have hw : w=0 := by omega
    have h := layout.wide
    rw [hw] at h
    norm_num at h
  have eq : (actual B.policy snap : Word w)=(testResult B m:Word w) := by
    rw [←mode_eval B.policy snap (0 : Word w)]
    exact (eval_below _ 0 (B.tests.after m) snap layout.fits
      (fun i hi => ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hi))).trans
      (B.tests.mode m 0 positive layout.stop layout.excess layout.payload)
  have small : testResult B m<4 := by unfold testResult selectMode; split_ifs <;> decide
  have same := congrArg Fin.val eq
  simpa only [Fin.val_cast_of_lt ((actual_lt B.policy snap).trans_le layout.wide),
    Fin.val_cast_of_lt (small.trans_le layout.wide),snap] using same

/-- Actual outer mode one determines the two low comparisons after the ordered
sum scans, including the second check's distinct input memory. -/
theorem observed_low (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (layout : TestRoom (repair C (.outer p h)) w) (hit : observedMode C mem p h=1) :
    let a := Attempt.outer p h
    let B := repair C a
    let m := prepared C a (trialState C mem p h)
    B.tests.excess.high m = false ∧ (p<C.mesh.inject → B.tests.payload.high (B.tests.excess.after m) = false) := by
  intro a B m
  change actual B.policy (postSnapshot (C.layout a) B m)=1 at hit
  rw [post_result _ _ _ layout] at hit
  change selectMode B.tests.injection false _ _ _ _=1 at hit
  have quiet := advance_low _ _ _ _ _ hit
  exact ⟨quiet.1,fun early=>quiet.2 (decide_eq_true early)⟩

/-- Any mode-two vote, including a reserve repair, required a high discrepancy
word. A purchase or an inner advance required a low one. -/
theorem discrepancy_votes (L : Dispatch) (B : Repair q d) (m : Memory w) (layout : TestRoom B w) :
    let h := actual B.policy (postSnapshot L B m)
    let high := B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after m))
    (h=2 → high=true) ∧ ((h=3 ∨ B.tests.reserve=true ∧ h=1) → high=false) := by
  dsimp only
  rw [post_result L B m layout]
  generalize hi : B.tests.discrepancy.high (B.tests.payload.after (B.tests.excess.after m))=flag
  unfold testResult
  rw [hi]
  generalize i : B.tests.injection=inject
  generalize r : B.tests.reserve=res
  generalize v : bit B.tests.stop m=stop
  generalize x : B.tests.excess.high m=excess
  generalize y : B.tests.payload.high (B.tests.excess.after m)=pay
  cases inject <;> cases res <;> cases stop <;> cases excess <;> cases pay <;> cases flag <;> decide

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
