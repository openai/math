import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.Geometry.OrderedScanKernel
import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol

/-! A fixed instruction loop implements the signed-minor column scan, charging each
visited column, retaining responses in wire order, and stopping on the first restart. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments

variable {n : ℕ} {κ : Type*}

/-- The scalar oracle stores its history newest first. -/
def scanHistory (packet : κ → List ℚ) (xs : List (κ × ℚ)) (h : Contract.History ℚ) : Contract.History ℚ :=
  (xs.map (fun p => (packet p.1,[0,p.2]))).reverse ++ h

/-- A scalar execution relation with a charged cost and a live oracle history. -/
abbrev ColumnExecution := Memory ℚ → Contract.History ℚ → ℕ → Memory ℚ → Contract.History ℚ → Prop

/-- A zero determinant skips the service. Every nonzero determinant transmits exactly
one canonical packet, either supplying the next value or stopping this scan. -/
def ColumnActionFor (bodyRun : ColumnExecution) (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ) (C : ℕ) : Prop :=
  ∀ (j : Fin n) (v : Fin n → ℚ) (m : Memory ℚ) (h : Contract.History ℚ), I j.val v m →
    if raw j=0 then ∃ t c, c≤C ∧ bodyRun m h c t h ∧ I (j.val+1) v t
    else ∃ t c ans, c≤C ∧ bodyRun m h c t ((packet (key j), reply ans)::h) ∧
      match ans with
      | none => stop t
      | some q => I (j.val+1) (Function.update v j q) t

/-- Actual unmarked executions of one candidate column. -/
abbrev ColumnAction (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ) (P : Memory ℚ → Prop)
    (body : Segment) (o : ScalarOracle ℚ) (C : ℕ) : Prop :=
  ColumnActionFor (Runs body o P) I stop raw key packet C

/-- The scalar history and the typed request trace describe the same exit. -/
def ScanExit (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (packet : κ → List ℚ) (t : Memory ℚ) (h final : Contract.History ℚ)
    (xs : List (κ × ℚ)) : Sum κ (Fin n → ℚ) → Prop
  | .inl a => stop t ∧ final = (packet a,[1]) :: scanHistory packet xs h
  | .inr vals => I n vals t ∧ final = scanHistory packet xs h

/-- The numerical and history induction for a charged column loop. The two supplied
rules are its stop and continue instructions; both ordinary and marked RAM executions
use precisely these instruction costs. -/
theorem scan_loop_with (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ) (P : Memory ℚ → Prop)
    (bodyRun loopRun : ColumnExecution) (C : ℕ)
    (stopRule : ∀ m h, P m → (Cond.addrLT 90 130).test m=false → loopRun m h 1 m h)
    (stepRule : ∀ {m u t h mid dest c k}, (Cond.addrLT 90 130).test m=true →
      bodyRun m h c u mid → loopRun u mid k t dest → loopRun m h (1+c+1+k) t dest)
    (live : ∀ i v (m : Memory ℚ), I i v m → P m ∧ m.index 90=i ∧ m.index 130=n)
    (stopped : ∀ m, stop m → P m ∧ m.index 90=n ∧ m.index 130=n)
    (action : ColumnActionFor bodyRun I stop raw key packet C)
    (i : ℕ) (hi : i≤n) (v : Fin n → ℚ) (m : Memory ℚ) (hist : Contract.History ℚ) (start : I i v m) :
    ∃ t final cost xs out, cost ≤ (n-i)*(C+2)+1 ∧
      loopRun m hist cost t final ∧
      MinorQuery.Run (MinorQuery.readColumns key (tailColumns raw i) v) xs out ∧
      ScanExit I stop packet t hist final xs out :=
  ScanKernel.scan_loop_with id I stop raw key packet P bodyRun loopRun C stopRule stepRule
    live stopped action i hi v m hist start

/-- Ordinary branch, jump, and false-guard steps are all counted. A previously
consumed history is preserved on both the answering and restart paths. -/
theorem scan_loop (I : ℕ → (Fin n → ℚ) → Memory ℚ → Prop) (stop : Memory ℚ → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List ℚ) (P : Memory ℚ → Prop)
    (body : Segment) (o : ScalarOracle ℚ) (C : ℕ)
    (live : ∀ i v (m : Memory ℚ), I i v m → P m ∧ m.index 90=i ∧ m.index 130=n)
    (stopped : ∀ m, stop m → P m ∧ m.index 90=n ∧ m.index 130=n)
    (action : ColumnAction I stop raw key packet P body o C)
    (i : ℕ) (hi : i≤n) (v : Fin n → ℚ) (m : Memory ℚ) (hist : Contract.History ℚ) (start : I i v m) :
    ∃ t final cost xs out, cost ≤ (n-i)*(C+2)+1 ∧
      Runs (.loop (.addrLT 90 130) body) o P m hist cost t final ∧
      MinorQuery.Run (MinorQuery.readColumns key (tailColumns raw i) v) xs out ∧
      ScanExit I stop packet t hist final xs out :=
  scan_loop_with I stop raw key packet P (Runs body o P) (Runs (.loop (.addrLT 90 130) body) o P) C
    (fun _ _ hm hc => Runs.loopFalse _ _ hm hc) (fun hc e t => Runs.loopTrue hc e t)
    live stopped action i hi v m hist start

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
