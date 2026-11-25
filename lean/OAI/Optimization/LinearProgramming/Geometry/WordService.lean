import OAI.Optimization.LinearProgramming.Geometry.PriceStep
import OAI.Optimization.LinearProgramming.Contraction.BisectionRAMDecode
import OAI.Optimization.LinearProgramming.Recovery.Restart

/-! Interpret the literal price-query words of the sealed sign learner with the
persistent geometric minor service. Only canonical words occur in the completed run. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract OracleSpec Matrix Recovery
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def toReply (ans : Option Bool) (state : Contract.History ℚ) : Recovery.Reply (Contract.History ℚ) :=
  match ans with
  | none => .restart state
  | some b => .answer b state

noncomputable def serveWord (S : Service D E) (state : Contract.History ℚ) (w : Word) : Recovery.Reply (Contract.History ℚ) :=
  match Contraction.BisectionRAM.readQuery n w with
  | none => .answer false state
  | some q => toReply (S.priceStep state q).1 (S.priceStep state q).2

@[simp] theorem serveWord_priceQuery (S : Service D E) (hist : Contract.History ℚ) (i : Fin n) (p : Fin n → ℚ) :
    S.serveWord hist (priceQuery i p) = toReply (S.priceStep hist ⟨p,i⟩).1 (S.priceStep hist ⟨p,i⟩).2 := by
  let q : PriceGame.Query n := ⟨p,i⟩
  change (match Contraction.BisectionRAM.readQuery n (priceQuery q.index q.prices) with
    | none => Recovery.Reply.answer false hist
    | some q => toReply (S.priceStep hist q).1 (S.priceStep hist q).2) = _
  rw [Contraction.BisectionRAM.readQuery_price]

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
