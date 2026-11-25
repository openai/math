import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProbeReportSockets

namespace OAI
/-! # Public socket ordinals and their original circuit sites -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets
variable {h W k attempts : ℕ}
abbrev PaidPorts (S : PurchaseSampler) (h W k attempts : ℕ) :=
  (Free S h (2^W) k × Bool) ⊕ (StageColumns h (2^W) × Role k attempts)
abbrev GoodPorts (h W k : ℕ) := (Fin (2^h) × Bool) ⊕ (StageColumns h (2^W) × (Fin k×Bool))
abbrev CatPorts (h W k : ℕ) := (Columns h (2^W)×Fin k) × Bool
abbrev Public (S : PurchaseSampler) (h W k attempts : ℕ) := PaidPorts S h W k attempts ⊕ (GoodPorts h W k ⊕ CatPorts h W k)

/-- Enumerate the public directory with the product and sum orders of its
original component tables. -/
noncomputable instance publicFintype (S : PurchaseSampler) (h W k attempts : ℕ) :
    Fintype (Public S h W k attempts) := by
  classical
  letI : Fintype (StageColumns h (2^W)) := inferInstance
  letI : Fintype (Columns h (2^W)) := inferInstance
  letI : Fintype (Fixed h (2^W)) := inferInstance
  letI : Fintype (Sample S h (2^W)) := inferInstance
  letI : Fintype (Free S h (2^W) k) := inferInstance
  letI : Fintype (PaidPorts S h W k attempts) := inferInstance
  letI : Fintype (GoodPorts h W k) := inferInstance
  letI : Fintype (CatPorts h W k) := inferInstance
  exact inferInstanceAs (Fintype (PaidPorts S h W k attempts ⊕ (GoodPorts h W k ⊕ CatPorts h W k)))

def goodsSite : GoodPorts h W k→Site h (2^W) k
  | .inl (p,false)=>(.inl p,none)
  | .inl (p,true)=>(.inr (.inr p),none)
  | .inr (u,l)=>(.inr (.inl u),match u.2.2 with | .inl _=>none | .inr _=>some l)

def catSite : CatPorts h W k→Site h (2^W) k := fun ((c,i),b)=>(c,some (i,b))

abbrev name := siteNumber h (2^W) k

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles
end

end OAI
