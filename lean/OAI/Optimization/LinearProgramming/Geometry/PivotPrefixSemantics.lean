import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract

/-! The prefix loop uses the same control and storage induction for ordinary traces and
for traces that additionally validate an ABI at each scalar query instruction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM RAM.Block Contract OracleSegments

abbrev PrefixTrace := Segment → (Memory ℚ → Prop) → Memory ℚ → Contract.History ℚ → ℕ → Memory ℚ → Contract.History ℚ → Prop

/-- The six scalar-free control operations and safety weakening used in the prefix proof. -/
structure TraceRules (tr : PrefixTrace) : Prop where
  core {P : Memory ℚ → Prop} {b : Block} {m t : Memory ℚ} {k : ℕ} : Eval P b m k t → ∀ h, tr (.core b) P m h k t h
  weaken {b P Q m h k t h'} : tr b P m h k t h' → (∀ z, P z → Q z) → tr b Q m h k t h'
  seq {a b P m h k t h' l z h''} : tr a P m h k t h' → tr b P t h' l z h'' → tr (.seq a b) P m h (k+l) z h''
  branchTrue {a b : Segment} {c : Cond} {P m h k t h'} : c.test m = true → tr a P m h k t h' → tr (.branch c a b) P m h (1+k+1) t h'
  branchFalse {a b : Segment} {c : Cond} {P m h k t h'} : c.test m = false → tr b P m h k t h' → tr (.branch c a b) P m h (1+k) t h'
  loopFalse {P m h} (c : Cond) (b : Segment) : P m → c.test m = false → tr (.loop c b) P m h 1 m h
  loopTrue {c : Cond} {b P m h k t h' l z h''} : c.test m = true → tr b P m h k t h' → tr (.loop c b) P t h' l z h'' →
    tr (.loop c b) P m h (1+k+1+l) z h''

theorem ordinaryRules (o : ScalarOracle ℚ) : TraceRules (fun b => Runs b o) where
  core x h := Runs.core x o h
  weaken x h := Runs.weaken x h
  seq x y := Runs.seq x y
  branchTrue cond x := Runs.branchTrue cond x
  branchFalse cond x := Runs.branchFalse cond x
  loopFalse cond body safe off := Runs.loopFalse cond body safe off
  loopTrue cond x y := Runs.loopTrue cond x y

/-- Upgrade the particular execution of a batch returned by the original mathematical
contract. The trace cost, terminal memory, and complete oracle history are fixed. -/
def BatchAnnotation {r n : ℕ} (tr : PrefixTrace) (batch : Segment) (o : ScalarOracle ℚ)
    (base : Memory ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (B extra : ℕ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop) : Prop :=
  ∀ (a : ℕ) (ha : a < r) (rows : Fin a → PivotRow n) (m : Memory ℚ) (hist : Contract.History ℚ) (H : ℕ),
    Stored base m rows price B → (D.submatrix (Fin.castLE (Nat.le_of_lt ha)) (fun j => (rows j).pivot)).det ≠ 0 →
    Aux m hist → RowRAM.Within H m → ∀ t final k,
      Runs batch o (RowRAM.Within (H+extra)) m hist k t final → tr batch (RowRAM.Within (H+extra)) m hist k t final

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
