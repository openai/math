import OAI.Hierarchy.PhysicalTracePins
import OAI.Hierarchy.TracePhysicalSiteCount
import OAI.Hierarchy.TraceNativeScale
import OAI.Hierarchy.TraceRecordScale

namespace OAI
/-! # The number of terminal factors and external input bits per factor -/

namespace Hierarchy.GridPhysicalSelector
open ThreeFlat Diagonal Diagonal.PhysicalStage
open Filter TraceDistribution Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
variable {F : Type} [Field F]

/-- The number of true factors and the number of external bits owned by
each one both fit the three-fifths power cap on the same physical history. -/
theorem physical_factor_budget [Fintype F] (B : Block F) {u s : ℕ → ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {k pc regs words N base fuel : ℕ}
      (hk : 2≤k+1) (_axes : k+1=u w+1-w/2) (M : Machine (64*w) pc regs words)
      (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (passes : B.blockCharge*s w≤k+1),
      let r := Physical.nativeRun B hk M fit hF st (s w) passes
      let L := layout M fit hF st
      ∀ h : r.plan.History, Fintype.card (r.plan.finish h).Site ≤ 2^(3*w/5) ∧
        ∀ (n : ℕ) (hn : n≤N) (v : (r.plan.finish h).Site),
          Nat.card {j : Fin n // r.plan.destination h
            (PairedCursor.owner L ⟨j.val,j.isLt.trans_le hn⟩)=v} ≤ 2^(3*w/5) := by
  filter_upwards [TraceAdmission.record_room scale 1, pin_room scale B.blockCharge] with w sites pins
  intro k pc regs words N base fuel hk axes M fit hF st passes r L h
  refine ⟨?_, fun n hn v => (Physical.repeated_native_pins B hk M fit hF st (s w) passes hn h v).trans pins⟩
  refine (Physical.run_sites B hk (w/2) _ _ _ passes h).trans ?_
  rw [axes]
  refine le_trans ?_ sites
  have left : 1≤1*(s w+1) := by omega
  have right : 1≤64*w+1 := by omega
  calc
    (u w+1-w/2)*2^(u w+1-w/2) ≤ 1+(u w+1-w/2)*2^(u w+1-w/2) := by omega
    _ = 1*(1+(u w+1-w/2)*2^(u w+1-w/2))*1 := by simp
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ left) right

end Hierarchy.GridPhysicalSelector

end OAI
