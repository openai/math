import OAI.ThreeFlat.Diagonal.RefreshStageRuns
import OAI.ThreeFlat.Diagonal.RefreshStageWork
import OAI.ThreeFlat.RAM.HeaderScanLayout

namespace OAI
/-! # Exact scan times for the directory endpoints known at refresh boot -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorExpr
open RAM.MotifRows RefreshDemandRows
variable {W a h k : ℕ}

noncomputable def preScans (cur : Word W) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : Scans W :=
  .next (.one ⟨12,13,closed (splitShifts (mPort a) cur)⟩) (.one ⟨2,18,closed (choiceWords cur base size)⟩)

noncomputable def postScans (cur : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad K : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j,Fin (size j) → Fin (mPort a) → Fin h → ℕ) : Scans W :=
  let width := generateWidth (input cur) (field cur 8) (index cur 19) (field cur 1) pad K base size bits pool
  .next (.one ⟨14,16,graphWords cur E pad⟩) (.next (.one ⟨19,17,closed width⟩)
    (.one ⟨3,20,closed (sparseCopy (mPort a) h pad cur)⟩))

def recordScans (cur : Word W) (m d K : ℕ) : Scans W :=
  .next (.one ⟨34,35,closed (Records.kernel cur)⟩) (.next (.one ⟨36,37,closed (Records.motif cur m K)⟩)
    (.next (.one ⟨38,39,closed (Records.halfHeader cur d)⟩) (.one ⟨40,41,closed (Records.halves cur d)⟩)))

@[simp] theorem pre_pipeline (cur : Word W) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : (preScans cur base size).pipeline cur=preparation cur base size := rfl

@[simp] theorem post_pipeline (cur : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad K : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j,Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    (postScans cur E pad K base size bits pool).pipeline cur=publication cur E pad K base size bits pool := rfl

@[simp] theorem record_pipeline (cur : Word W) (m d K : ℕ) :
    (recordScans cur m d K).pipeline cur=Records.pipeline cur m d K := rfl

set_option maxHeartbeats 2000000 in
/-- The nine complete native scans contribute a linear cost in the actual
output words. The coefficient is fixed before choosing the RAM word width. -/
theorem scan_time (E : SlotGraph (Fin (mPort a)) h) (pad K : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j,Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    ∃ B : ℕ, ∀ W (cur : Word W) (f : ℕ→ℕ),
      (preScans cur base size).time f + (postScans cur E pad K base size bits pool).time f +
        (recordScans cur (mPort a) (1+h+pad) K).time f ≤
      99+B*(f 13+f 18+f 16+f 17+f 20+f 35+f 37+f 39+f 41) := by
  obtain ⟨B,hB⟩ := uniform_row_cost E pad K base size bits pool
  refine ⟨B,?_⟩
  intro W cur f
  let e := compiledRows cur E pad K base size bits pool
  let offsets : Fin 9→ℕ := ![13,18,16,17,20,35,37,39,41]
  have term (j : Fin 9) : f (offsets j)*(2*(e j).binds+4)≤B*f (offsets j) := by
    rw [Nat.mul_comm (f (offsets j))]
    exact Nat.mul_le_mul_right _ (hB W cur j).2.2
  have q0 : f 13*(2*(e 0).binds+4) ≤ B*f 13 := term 0
  have q1 : f 18*(2*(e 1).binds+4) ≤ B*f 18 := term 1
  have q2 : f 16*(2*(e 2).binds+4) ≤ B*f 16 := term 2
  have q3 : f 17*(2*(e 3).binds+4) ≤ B*f 17 := term 3
  have q4 : f 20*(2*(e 4).binds+4) ≤ B*f 20 := term 4
  have q5 : f 35*(2*(e 5).binds+4) ≤ B*f 35 := term 5
  have q6 : f 37*(2*(e 6).binds+4) ≤ B*f 37 := term 6
  have q7 : f 39*(2*(e 7).binds+4) ≤ B*f 39 := term 7
  have q8 : f 41*(2*(e 8).binds+4) ≤ B*f 41 := term 8
  change (11+f 13*(2*(e 0).binds+4)+(11+f 18*(2*(e 1).binds+4)))+
    (11+f 16*(2*(e 2).binds+4)+(11+f 17*(2*(e 3).binds+4)+(11+f 20*(2*(e 4).binds+4))))+
    (11+f 35*(2*(e 5).binds+4)+(11+f 37*(2*(e 6).binds+4)+(11+f 39*(2*(e 7).binds+4)+
      (11+f 41*(2*(e 8).binds+4)))))≤_
  conv_rhs => simp only [Nat.mul_add]
  omega

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
