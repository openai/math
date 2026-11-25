import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCore
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCode
import OAI.Optimization.LinearProgramming.Geometry.BorderScan
import OAI.Optimization.LinearProgramming.Geometry.BorderSchedule
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixRAM

/-! The concrete signed-minor and scalar-oracle implementation of the prefix ABI. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments Matrix Compression Compression.MinorLoad

variable {r s n B : ℕ}

/-- The scan shares one response guard for actual replies and for zero entries skipped
without a request. The complete register guard also covers transmitted array indices. -/
theorem scan_guards (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) (H e g : ℕ) (o : ScalarOracle ℚ)
    (oracle : Responds D E (fun q => ratBits q ≤ g) o) :
    (∀ q : ℚ, ratBits q ≤ max 3 g → ratBits q ≤ H+batchIncrement n e g) ∧ ratBits (0:ℚ) ≤ max 3 g ∧
    (∀ i ≤ n, ratBits (i:ℚ) ≤ H+batchIncrement n e g) ∧ Responds D E (fun q => ratBits q ≤ max 3 g) o := by
  refine ⟨?_,?_,?_,?_⟩
  · intro q h; unfold batchIncrement; omega
  · change 3 ≤ max 3 g; exact le_max_left _ _
  · intro i h; exact (addr_width i).trans (by unfold batchIncrement; omega)
  · intro h u
    obtain ⟨a,reply,legal⟩ := oracle h u
    exact ⟨a,reply,fun q ans => (legal q ans).trans (le_max_right _ _)⟩

/-- The concrete program satisfies the full adaptive batch contract: it derives every
signed minor from the original matrix and transmits only actual canonical minor packets. -/
theorem batch_sound {L : Layout r n} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (price : Fin n → ℚ) (base : Memory ℚ) (e g : ℕ) (o : ScalarOracle ℚ) (input : Inputs L D price B base)
    (hD : LinearIndependent ℚ D.row) (hrn : r≤n) (hmat : ∀ i j, ratBits (D i j) ≤ e)
    (hprice : ∀ j, ratBits (price j) ≤ e) (oracle : Responds D E (fun q => ratBits q ≤ g) o) :
    PivotPrefixRAM.BatchSound batchProgram o (keyPacket D E) base D price B (batchLocalWidth n e g) (batchIncrement n e g)
      (batchTime r n) (fun m _ => PreservesInput L base m) := by
  intro k hk rows m hist H
  dsimp only
  intro previous nonsing keep safe
  let J := fun i => (rows i).pivot
  let A := D.submatrix (Fin.castLE hk) id
  let W := H+batchIncrement n e g
  let P := fun q : ℚ => ratBits q ≤ W
  let allowed := fun q : ℚ => ratBits q ≤ max 3 g
  obtain ⟨extender,zero,counts,responds⟩ := scan_guards D E H e g o oracle
  obtain ⟨v,cv,hcv,eval,vs,keepV,raw⟩ := prepare_run e g H input hk hrn hmat previous keep safe
  have src : Sources L v D hk J price := ⟨input.ready vs keepV,raw,input.prices_live keepV⟩
  have prepared := Runs.core eval o hist
  obtain ⟨t,final,c,xs,out,hc,rpc,read,meaning⟩ := scan_runs v P allowed o hist D E J price hk hrn src (Runs.finish prepared) extender zero counts responds
  have runBatch := Runs.seq prepared rpc
  have scanBound : scanCost k n ≤ scanCost r n := by
    unfold scanCost candidateCost; gcongr
  have total : cv+c ≤ batchTime r n := by dsimp [batchTime]; omega
  have finishFrame {t : Memory ℚ} (h : ScanFrame L v t) := rows_after_scan input vs hk.le keepV h
  refine ⟨t,final,_,total,runBatch,?_⟩
  cases out with
  | inl key =>
    obtain ⟨stopped,history⟩ := meaning
    obtain ⟨stored,persist⟩ := finishFrame stopped.toScanFrame
    exact ⟨persist,stored,Or.inr ⟨xs,key,stopped.status,step_of_restarted A J price read,history⟩⟩
  | inr vals =>
    obtain ⟨finished,history⟩ := meaning
    obtain ⟨stored,persist⟩ := finishFrame finished.toScanFrame
    have linear : LinearIndependent ℚ A.row := hD.comp (Fin.castLE hk) (Fin.castLE_injective hk)
    obtain ⟨row,req,assigned,rawEq,logs⟩ := step_of_scanned A J price linear nonsing vals read
    have triples := (input.ready stored persist).tripleAddr
    have correct := packed_of_scan finished triples rawEq logs (Nat.le_trans hk hrn) (fun i j => hmat (Fin.castLE hk i) j) hprice
    exact ⟨persist,stored,Or.inl ⟨xs,stageExtension A J vals,row,finished.status,req,assigned,correct,history⟩⟩

/-- The full fixed-program price-prefix execution queries the scalar oracle only for
the prescribed bounded minor replies. -/
theorem prefix_runs {L : Layout r n} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (price : Fin n → ℚ) (base : Memory ℚ) (e g H : ℕ) (o : ScalarOracle ℚ) (hist : Contract.History ℚ)
    (input : Inputs L D price B base) (hD : LinearIndependent ℚ D.row) (hrn : r≤n)
    (hmat : ∀ i j, ratBits (D i j) ≤ e) (hprice : ∀ j, ratBits (price j) ≤ e)
    (oracle : Responds D E (fun q => ratBits q ≤ g) o) (safe : RowRAM.Within H base) :
    ∃ t final k, k ≤ r*PivotPrefixRAM.stepCost n B (batchTime r n)+6 ∧
      Runs (PivotPrefixRAM.program batchProgram) o (RowRAM.Within
        (H+r*PivotPrefixRAM.stepWidth n (batchLocalWidth n e g) B (batchIncrement n e g))) base hist k t final ∧
      PreservesInput L base t ∧ PivotPrefixRAM.Outcome (keyPacket D E) base D price B hist t final :=
  PivotPrefixRAM.run batchProgram o (keyPacket D E) D price base hist _ input.prefixLayout hD safe input.aux_stable
    (fun _ _ _ => rfl) (batch_sound D E price base e g o input hD hrn hmat hprice oracle)

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
