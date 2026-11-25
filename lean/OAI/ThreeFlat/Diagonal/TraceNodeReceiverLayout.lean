import OAI.ThreeFlat.Diagonal.TraceNodeBankLayout
import OAI.Hierarchy.TraceReceiverAge
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # The receiver's S41 controls, S42 header, S43 charge array and S44 node array -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

/-- The two outputs have exactly the bases read by the receiver's navigation code. -/
def receiverArchive (v lanes perLane pairs trace tariff cc hc mc : ℕ) : NodeArchive :=
  spacedArchive (TickWorkspace.base v 41) (TickWorkspace.base v 42) (TickWorkspace.base v 43)
    (TickWorkspace.base v 44) lanes perLane pairs trace tariff cc hc mc

theorem receiver_space {v w : ℕ} (hw : 1≤w) (small : 3*w≤v^10) (large : v^10≤5*w) :
    BankSpace (64*w) (TickWorkspace.base v 41) (TickWorkspace.base v 42) (TickWorkspace.base v 43)
      (TickWorkspace.base v 44) (TickWorkspace.base v 45) (traceUnit w) ∧
    TickWorkspace.base v 20+7*traceUnit w≤TickWorkspace.base v 41 ∧
    TickWorkspace.base v 40≤TickWorkspace.base v 41 := by
  have unit : 16≤traceUnit w := (trace_sector hw).1
  have stride : traceUnit w≤TickWorkspace.stride v := by
    unfold traceUnit TickWorkspace.stride
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega)) _
  have top : TickWorkspace.base v 45<2^(64*w) := calc
    _ ≤ 2^6*TickWorkspace.stride v := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(6+v^10*4) := by simp only [TickWorkspace.stride,pow_add,pow_mul]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨?_,?_,?_⟩
  · constructor <;> simp only [TickWorkspace.base] at * <;> omega
  · unfold TickWorkspace.base;omega
  · unfold TickWorkspace.base;omega

/-- The caller can use the same public age at every sufficiently large word width. -/
theorem receiver_space_at_age (w : ℕ) (hw : 64^10≤w) :
    let v := Hierarchy.TraceAdmission.receiverAge w
    BankSpace (64*w) (TickWorkspace.base v 41) (TickWorkspace.base v 42) (TickWorkspace.base v 43)
      (TickWorkspace.base v 44) (TickWorkspace.base v 45) (traceUnit w) ∧
    TickWorkspace.base v 20+7*traceUnit w≤TickWorkspace.base v 41 ∧
    TickWorkspace.base v 40≤TickWorkspace.base v 41 := by
  obtain ⟨small,large⟩ := Hierarchy.TraceAdmission.receiverAge_chart w hw
  exact receiver_space (by omega) (by omega) large

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
