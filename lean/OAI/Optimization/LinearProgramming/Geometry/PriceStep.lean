import OAI.Optimization.LinearProgramming.Geometry.MinorQueryExecute
import OAI.Optimization.LinearProgramming.Geometry.MinorQuery
import OAI.Optimization.LinearProgramming.Geometry.BorderServiceHistory
import OAI.Optimization.LinearProgramming.Geometry.QueryKeys
import OAI.Optimization.LinearProgramming.PriceGame.Model

/-! A deterministic price oracle derived from the online minor service and the
geometric query tree. Its state is exactly the scalar minor transcript. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract Matrix OracleSpec.MinorLog

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- Decode the returned tag at exactly the history preceding this request. -/
noncomputable def requestAt (S : Service D E) (h : Contract.History ℚ) (msg : List ℚ) : Option ℚ :=
  match decode D E msg with
  | none => none
  | some u => S.next (pastRequests D E h) u

@[simp] theorem requestAt_packet (S : Service D E) (h : Contract.History ℚ) (u : Index D E) :
    S.requestAt h (packet u.val)=S.next (pastRequests D E h) u := by
  simp [requestAt]

theorem oracle_requestAt (S : Service D E) (h : Contract.History ℚ) (msg : List ℚ) :
    S.oracle h msg=reply (S.requestAt h msg) := by
  unfold oracle requestAt
  cases decode D E msg <;> rfl

/-- The played trace includes every accepted answer and the first restarting key. -/
noncomputable def priceTrace (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n) :
    MinorQuery.Played (PivotKey n) Bool :=
  MinorQuery.execute (keyPacket D E) (fun h k => S.requestAt h (keyPacket D E k))
    (geometricMinorLabel D q.prices q.index) before

/-- Expose only the price label or a restart, together with the updated service history. -/
noncomputable def priceStep (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n) :
    Option Bool × Contract.History ℚ :=
  let z := S.priceTrace before q
  (z.out.elim (fun _ => none) some,z.history)

theorem priceTrace_spec (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n) :
    let z := S.priceTrace before q
    MinorQuery.Run (geometricMinorLabel D q.prices q.index) z.answers z.out ∧
    z.history=MinorQuery.recorded (keyPacket D E) z.answers z.out before :=
  MinorQuery.execute_spec (keyPacket D E) (fun h key => S.requestAt h (keyPacket D E key))
    (geometricMinorLabel D q.prices q.index) before

theorem priceTrace_answers (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n)
    (old : answersMatch S.oracle before) : answersMatch S.oracle (S.priceTrace before q).history :=
  MinorQuery.execute_answers (keyPacket D E) (fun h key => S.requestAt h (keyPacket D E key)) S.oracle
    (fun h key => S.oracle_requestAt h (keyPacket D E key)) (geometricMinorLabel D q.prices q.index) before old

theorem priceStep_of_run (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n)
    {xs : List (PivotKey n × ℚ)} {out : Sum (PivotKey n) Bool}
    (run : MinorQuery.Run (geometricMinorLabel D q.prices q.index) xs out)
    (ok : answersMatch S.oracle (MinorQuery.recorded (keyPacket D E) xs out before)) :
    S.priceStep before q=(out.elim (fun _ => none) some, MinorQuery.recorded (keyPacket D E) xs out before) := by
  have eq : S.priceTrace before q=⟨xs,out,MinorQuery.recorded (keyPacket D E) xs out before⟩ :=
    MinorQuery.execute_of_run _ _ _ (fun h k => S.oracle_requestAt h (keyPacket D E k)) run before ok
  simp only [priceStep,eq]

/-- Any common extension of the actual accepted minor replies reproduces the price
label. This proof does not need to rerun any matrix arithmetic. -/
theorem priceTrace_accept (S : Service D E) (before : Contract.History ℚ) (q : PriceGame.Query n) (b : Bool)
    (accepted : (S.priceStep before q).1=some b) (f : Compression.NonzeroPairMinor D E → ℚ)
    (agrees : ∀ e∈(S.priceTrace before q).answers, prefixAssignment D E f e.1=e.2) :
    (geometricLabel D E q.prices q.index).eval f=b := by
  have h := (S.priceTrace_spec before q).1
  cases out : (S.priceTrace before q).out with
  | inl k => simp [priceStep,out] at accepted
  | inr v =>
    have eq : v=b := by simpa [priceStep,out] using accepted
    rw [out] at h
    exact (geometricLabel_eval D E f q.prices q.index).trans ((h.eval_of_extends _ agrees).trans eq)

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
