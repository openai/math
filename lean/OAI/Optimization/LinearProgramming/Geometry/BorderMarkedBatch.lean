import OAI.Optimization.LinearProgramming.Geometry.PivotMarkedPrefix
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchRAM
import OAI.Optimization.LinearProgramming.Geometry.BorderScanMarked

/-! Actual logical RAM memory at every physical named-minor exchange of the prefix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Contract OracleSegments

variable {r s n B : ℕ}

/-- The determinant-table preparation is an ordinary RAM block. The only scalar
exchanges occur in the marked streaming scan of its resulting signed-minor tape. -/
theorem batch_marked_inputs {L : Layout r n} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (price : Fin n → ℚ) (base : Memory ℚ) (e g : ℕ) (o : ScalarOracle ℚ) (input : Inputs L D price B base)
    (hrn : r ≤ n) (hmat : ∀ i j, ratBits (D i j) ≤ e) (oracle : Responds D E (fun q => ratBits q ≤ g) o) :
    PivotPrefixRAM.MarkedBatchInputs MinorSite batchProgram o base D price B (batchIncrement n e g)
      (fun m _ => PreservesInput L base m) := by
  intro a ha rows m hist H stored _ kept safe
  let J := fun i => (rows i).pivot
  obtain ⟨v,cv,_,eval,storeV,keptV,raw⟩ := prepare_run e g H input ha hrn hmat stored kept safe
  have src : Sources L v D ha J price := ⟨input.ready storeV keptV,raw,input.prices_live keptV⟩
  obtain ⟨extender,zero,indices,responds⟩ := scan_guards D E H e g o oracle
  let P (q : ℚ) := ratBits q ≤ H+batchIncrement n e g
  obtain ⟨t,final,c,scanRun⟩ := scan_marked_exists v P (fun q => ratBits q ≤ max 3 g) o hist D E J price ha hrn src
    eval.safe_end extender zero indices responds
  exact ⟨t,final,cv+c,(MarkedRuns.core (mark := MinorSite) eval o hist).seq scanRun⟩

/-- The finite prefix machine carries the native-service ABI at each query, as well as
the complete computation-time, register-width, transcript, and public-output guarantees. -/
theorem prefix_runs_marked {L : Layout r n} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (price : Fin n → ℚ) (base : Memory ℚ) (e g H : ℕ) (o : ScalarOracle ℚ) (hist : Contract.History ℚ)
    (input : Inputs L D price B base) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n)
    (hmat : ∀ i j, ratBits (D i j) ≤ e) (hprice : ∀ j, ratBits (price j) ≤ e)
    (oracle : Responds D E (fun q => ratBits q ≤ g) o) (safe : RowRAM.Within H base) :
    ∃ t final k, k ≤ r*PivotPrefixRAM.stepCost n B (batchTime r n)+6 ∧
      MarkedRuns MinorSite (PivotPrefixRAM.program batchProgram) o (RowRAM.Within
        (H+r*PivotPrefixRAM.stepWidth n (batchLocalWidth n e g) B (batchIncrement n e g))) base hist k t final ∧
      PreservesInput L base t ∧ PivotPrefixRAM.Outcome (keyPacket D E) base D price B hist t final :=
  PivotPrefixRAM.run_marked MinorSite batchProgram o (keyPacket D E) D price base hist _ input.prefixLayout hD safe input.aux_stable
    (fun _ _ _ => rfl) (batch_sound D E price base e g o input hD hrn hmat hprice oracle)
    (batch_marked_inputs D E price base e g o input hrn hmat oracle)

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
