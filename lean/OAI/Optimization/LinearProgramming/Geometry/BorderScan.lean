import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCode
import OAI.Optimization.LinearProgramming.Geometry.BorderScanLoop

/-! The actual rational triple materializer for one prefix of a signed-minor family. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments Matrix

variable {r s n k : ℕ}

/-- Entire stage scan, including the program initialization and all live scalar traffic.
The total trace consists exactly of the accepted packets followed by at most one restart. -/
theorem scan_runs {L : Layout r n} (m : Memory ℚ) (P A : ℚ → Prop) (o : ScalarOracle ℚ)
    (history : Contract.History ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (J : Fin k → Fin n) (price : Fin n → ℚ) (hr : k+1 ≤ r) (hrn : r ≤ n) (src : Sources L m D hr J price)
    (hm : m.AllData P) (hAP : ∀q,A q → P q) (hz : A 0) (hn : ∀i ≤ n,P (i:ℚ)) (responds : Responds D E A o) :
    let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
    ∃ t final c xs out, c ≤ scanCost k n ∧ Runs scan o (Memory.AllData P) m history c t final ∧
      MinorQuery.Run (MinorQuery.readColumns (pivotKey J) (tailColumns raw 0) 0) xs out ∧
      match out with
      | .inl z => ScanStopped L m t ∧ final=(keyPacket D E z,[1])::scanHistory (keyPacket D E) xs history
      | .inr vals => ScanReady L m raw price A n vals t ∧ final=scanHistory (keyPacket D E) xs history := by
  let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
  let I (i : ℕ) (v : Fin n → ℚ) (u : Memory ℚ) := ScanReady L m raw price A i v u ∧ u.AllData P
  let stop (u : Memory ℚ) := ScanStopped L m u ∧ u.AllData P
  have action : ColumnAction I stop raw (pivotKey J) (keyPacket D E) (Memory.AllData P) candidate o (candidateCost k n) := by
    intro j v z h hzv
    obtain ⟨active,safe⟩ := hzv
    have step := candidate_runs P A o h D E J price hr hrn src j v safe hAP hz hn responds active
    dsimp only at step
    change (if raw j=0 then _ else _) at step ⊢
    by_cases eq : raw j=0
    · rw [ite_eq_left eq] at step ⊢
      obtain ⟨t,c,cap,run,ok⟩ := step
      exact ⟨t,c,cap,run,ok,run.finish⟩
    · rw [ite_eq_right eq] at step ⊢
      obtain ⟨ans,t,c,cap,run,ok⟩ := step
      refine ⟨t,c,ans,cap,run,?_⟩
      cases ans <;> exact ⟨ok,run.finish⟩
  have init := Runs.core (BorderScatter.init_spec m hm) o history
  obtain ⟨t,final,c,xs,out,hc,run,tree,hout⟩ :=
    scan_loop I stop raw (pivotKey J) (keyPacket D E) (Memory.AllData P) candidate o (candidateCost k n)
    (fun _ _ _ h => ⟨h.2,h.1.cursor,(h.1.indices 130 (by decide) (by decide)).trans src.ready.width⟩)
    (fun _ h => ⟨h.2,h.1.finished,h.1.width⟩) action 0 (by omega) 0 (BorderScatter.initState m) history
    ⟨scanInit src.ready raw price A hz,init.finish⟩
  refine ⟨t,final,5+c,xs,out,by simp only [Nat.sub_zero] at hc; unfold scanCost; omega,init.seq run,tree,?_⟩
  cases out <;> exact ⟨hout.1.1,hout.2⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
