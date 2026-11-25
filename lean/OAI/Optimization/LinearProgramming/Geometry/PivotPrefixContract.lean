import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixMemory
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixTrace
import OAI.Optimization.LinearProgramming.Geometry.OracleSegments

/-! The ABI between the signed-minor/compression oracle and the finite pivot-prefix RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM RAM.Block Contract OracleSegments

/-- The external history is newest-first and records the actual encoded scalar traffic. -/
def answeredHistory {κ : Type*} (packet : κ → List ℚ) (xs : List (κ × ℚ)) (h : Contract.History ℚ) : Contract.History ℚ :=
  (xs.map (fun e => (packet e.1,[0,e.2]))).reverse ++ h

theorem answeredHistory_append {κ : Type*} (packet : κ → List ℚ) (xs ys : List (κ × ℚ)) (h : Contract.History ℚ) :
    answeredHistory packet (xs++ys) h = answeredHistory packet ys (answeredHistory packet xs h) := by
  simp [answeredHistory,List.append_assoc]

/-- Private service registers can be read again after every untouched-history computation. -/
def FrameStable (base : Memory ℚ) (r n : ℕ) (Aux : Memory ℚ → Contract.History ℚ → Prop) : Prop :=
  ∀ m t h, CallerFrame base m t r n → Aux m h → Aux t h

/-- The batch segment is charged on its actual scalar-oracle RAM program. A valid
batch either materializes every candidate, or returns the first restarting packet and
exactly the answered prefix that preceded it. -/
def BatchSound {r n : ℕ} (batch : Segment) (o : ScalarOracle ℚ) (packet : PivotKey n → List ℚ)
    (base : Memory ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (B L increment cost : ℕ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop) : Prop :=
  ∀ (a : ℕ) (ha : a < r) (rows : Fin a → PivotRow n) (m : Memory ℚ) (hist : Contract.History ℚ) (H : ℕ),
    let stage := pivotStep (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) price
    Stored base m rows price B → (D.submatrix (Fin.castLE (Nat.le_of_lt ha)) (fun j => (rows j).pivot)).det ≠ 0 →
    Aux m hist → RowRAM.Within H m →
    ∃ t final k, k ≤ cost ∧ Runs batch o (RowRAM.Within (H+increment)) m hist k t final ∧
      Aux t final ∧ Stored base t rows price B ∧
      ((∃ xs f row, t.index 139 = 0 ∧ MinorQuery.Run stage xs (.inr (some row)) ∧ MinorQuery.eval f stage = some row ∧
          PackedRow t row price L ∧ final = answeredHistory packet xs hist) ∨
       (∃ xs key, t.index 139 = 1 ∧ MinorQuery.Run stage xs (.inl key) ∧ final = (packet key,[1]) :: answeredHistory packet xs hist))

/-- A restarting scalar request never commits a partially produced row. On normal
return, every pivot and rational rounded row is in its advertised public location. -/
inductive Outcome {r n : ℕ} (packet : PivotKey n → List ℚ) (base : Memory ℚ) (D : Matrix (Fin r) (Fin n) ℚ)
    (price : Fin n → ℚ) (B : ℕ) (initialHistory : Contract.History ℚ) (t : Memory ℚ) (final : Contract.History ℚ) : Prop where
  | completed (xs : List (PivotKey n × ℚ)) (rows : Fin r → PivotRow n)
      (requests : MinorQuery.Run (pivotPrefix D price r le_rfl) xs (.inr (some rows)))
      (history : final = answeredHistory packet xs initialHistory) (status : t.index 139 = 0)
      (stored : Stored base t rows price B) : Outcome packet base D price B initialHistory t final
  | restarted (xs : List (PivotKey n × ℚ)) (key : PivotKey n) (a : ℕ) (ha : a < r) (rows : Fin a → PivotRow n)
      (requests : MinorQuery.Run (pivotPrefix D price r le_rfl) xs (.inl key))
      (history : final = (packet key,[1]) :: answeredHistory packet xs initialHistory) (status : t.index 139 = 1)
      (stored : Stored base t rows price B) : Outcome packet base D price B initialHistory t final

/-- Every real exchange, including the final restart if present, is accounted for by
the paper's at-most-one-request-per-column-per-row bound. -/
theorem Outcome.query_bound {r n B : ℕ} {packet : PivotKey n → List ℚ} {base t : Memory ℚ}
    {D : Matrix (Fin r) (Fin n) ℚ} {price : Fin n → ℚ} {hist final : Contract.History ℚ}
    (run : Outcome packet base D price B hist t final) : final.length ≤ hist.length+r*n := by
  cases run with
  | completed xs rows req h _ _ =>
    have hc := pivotPrefix_run_bound D price r le_rfl req
    simp [MinorQuery.restartCost] at hc
    simp [h,answeredHistory]; omega
  | restarted xs key a ha rows req h _ _ =>
    have hc := pivotPrefix_run_bound D price r le_rfl req
    simp [MinorQuery.restartCost] at hc
    simp [h,answeredHistory]; omega

/-- For every assignment extending the received packets, the exact same machine rows
satisfy the pivot laws for the original matrix and prices. -/
theorem Outcome.completed_spec {r n B : ℕ} {packet : PivotKey n → List ℚ} {base t : Memory ℚ}
    {D : Matrix (Fin r) (Fin n) ℚ} {price : Fin n → ℚ} {hist final : Contract.History ℚ}
    (run : Outcome packet base D price B hist t final) (status : t.index 139 = 0) (independent : LinearIndependent ℚ D.row) :
    ∃ xs rows, final = answeredHistory packet xs hist ∧ Stored base t rows price B ∧
      ∀ f, (∀ e ∈ xs, f e.1 = e.2) → PivotSystemSpec D price f le_rfl rows := by
  cases run with
  | completed xs rows req h _ stored =>
    refine ⟨xs,rows,h,stored,?_⟩
    intro f ext
    obtain ⟨rs,eq,spec⟩ := pivotPrefix_run_correct D price r le_rfl independent req f ext
    cases Option.some.inj eq
    exact spec
  | restarted _ _ _ _ _ _ _ h _ => omega

/-- Address 14 is a disposable loop cursor. A restart sets it to the total rank,
leaving address 128 equal to the number of rows actually committed. -/
def controlMemory (m : Memory ℚ) (src : ℕ) : Memory ℚ := m.putIndex 14 (m.index src)

theorem Stored.control {n a B : ℕ} {base m : Memory ℚ} {rows : Fin a → PivotRow n} {price : Fin n → ℚ}
    (hs : Stored base m rows price B) (high : 256 ≤ base.index 136) (src : ℕ) : Stored base (controlMemory m src) rows price B := by
  refine ⟨hs.length,hs.rowCursor,hs.pivotCursor,?_,?_,hs.rounded⟩
  · intro i lo hi h135 h137 h139
    simpa [controlMemory,show i ≠ 14 by omega] using hs.permanent i lo hi h135 h137 h139
  · intro j
    simpa [controlMemory,show base.index 136+j.val ≠ 14 by omega] using hs.pivots j

theorem CallerFrame.control (base m : Memory ℚ) (r n src : ℕ) : CallerFrame base m (controlMemory m src) r n := by
  refine ⟨fun _ _ _ => rfl,?_⟩
  intro i hi _; simp [controlMemory,show i ≠ 14 by omega]

def success : Segment := .seq (.core acceptedStage) (.core (.op (.addrCopy 14 128)))

def iteration (batch : Segment) : Segment := .seq batch <| .seq (.core (.op (.addrConst 15 1)))
  (.branch (.addrLT 139 15) success (.core (.op (.addrCopy 14 129))))

def prefixLoop (batch : Segment) : Segment := .loop (.addrLT 14 129) (iteration batch)

/-- Finite uniform program. Neither stage count nor matrix dimensions change the
emitted instructions. They are read from the address registers at run time. -/
def program (batch : Segment) : Segment := .seq (.core initializePrefix)
  (.seq (.core (.op (.addrCopy 14 128))) (prefixLoop batch))

def stepCost (n B batchCost : ℕ) : ℕ := batchCost+n*(32*B+210)+33

def stepWidth (n L B extra : ℕ) : ℕ := extra+PivotStageRAM.widthIncrement n L B

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
