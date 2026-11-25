import OAI.Optimization.LinearProgramming.Geometry.BorderLayout
import OAI.Optimization.LinearProgramming.Compression.MinorBatch

/-! Materialization of signed (possibly zero) prefix minors with ordinary RAM instructions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Compression Compression.MinorLoad Matrix

/-- Fall-through form: the descriptor block can precede this, and subsequent comparison or
packing code can use both the output tape and all the still-live geometric inputs. -/
theorem signed_border_batch {r n k : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (J : Fin k → Fin n)
    (L : Layout r n) (hr : k+1 ≤ r) (hrn : r ≤ n) (m : Memory ℚ)
    (ready : BatchInput (L.batch D hr J) m) (H E : ℕ)
    (hall : ∀ p, ratBits (m.data p) ≤ H) (hentry : ∀ i j, ratBits (D i j) ≤ E) :
    ∃ t cost, cost ≤ n*(2200*(n+1)^7+17)+2 ∧
      Block.Eval (fun v => ∀ p, ratBits (v.data p) ≤ max H (detRegisterBits n E))
        (batchBlock determinantBlock) m cost t ∧
      (∀ j : Fin n, t.data (L.answers+j.val) = borderedMinor (D.submatrix (Fin.castLE hr) id) J j) ∧
      (∀ p, 7 ≤ p → p < L.answers → t.data p = m.data p) ∧
      (∀ p, 20 ≤ p → t.index p = m.index p) := by
  let batch := L.batch D hr J
  obtain ⟨t,cost,hc,run,ans,data,idx⟩ := batchBlock_bits_at determinantBlock fixedMinorCall batch m ready n E
    (max H (detRegisterBits n E)) (fun _ => ⟨hrn, le_rfl, hr.trans hrn⟩)
    (fun q => (hall q).trans (le_max_left ..)) (fun _ _ _ => hentry _ _) (le_max_right ..)
  refine ⟨t,cost,hc,run,?_,data,idx⟩
  intro j
  rw [borderedMinor_eq]
  exact ans j

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
