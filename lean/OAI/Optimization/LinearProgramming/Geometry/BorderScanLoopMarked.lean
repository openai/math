import OAI.Optimization.LinearProgramming.Geometry.BorderScanLoop
import OAI.Optimization.LinearProgramming.Geometry.MarkedSegments

/-! The signed-minor column loop retains the caller-memory certificate at every exchange. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments

variable {n : ℕ} {κ : Type*}

abbrev ColumnActionMarked (mark : QueryMark ℚ) (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop)
    (stop : Memory ℚ → Prop) (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ)
    (P : Memory ℚ → Prop) (body : Segment) (o : ScalarOracle ℚ) (C : ℕ) : Prop :=
  ColumnActionFor (MarkedRuns mark body o P) I stop raw key packet C

/-- Ordinary branch, jump, and false-guard steps are all counted. A previously
consumed history is preserved on both the answering and restart paths. -/
theorem scan_loop_marked {mark : QueryMark ℚ} (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ) (P : Memory ℚ → Prop)
    (body : Segment) (o : ScalarOracle ℚ) (C : ℕ)
    (live : ∀ i v (m : Memory ℚ), I i v m → P m ∧ m.index 90=i ∧ m.index 130=n)
    (stopped : ∀ m, stop m → P m ∧ m.index 90=n ∧ m.index 130=n)
    (action : ColumnActionMarked mark I stop raw key packet P body o C)
    (i : ℕ) (hi : i≤n) (v : Fin n → ℚ) (m : Memory ℚ) (hist : Contract.History ℚ) (start : I i v m) :
    ∃ t final cost xs out, cost ≤ (n-i)*(C+2)+1 ∧
      MarkedRuns mark (.loop (.addrLT 90 130) body) o P m hist cost t final ∧
      MinorQuery.Run (MinorQuery.readColumns key (tailColumns raw i) v) xs out ∧
      ScanExit I stop packet t hist final xs out :=
  scan_loop_with I stop raw key packet P (MarkedRuns mark body o P)
    (MarkedRuns mark (.loop (.addrLT 90 130) body) o P) C
    (fun _ _ hm hc => MarkedRuns.loopFalse _ _ hm hc) (fun hc e t => MarkedRuns.loopTrue hc e t)
    live stopped action i hi v m hist start

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
