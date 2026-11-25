import OAI.Optimization.LinearProgramming.Geometry.WirePriceCall
import OAI.Optimization.LinearProgramming.Geometry.WireMinorService
import OAI.Optimization.LinearProgramming.Geometry.ComparatorAccuracy
import OAI.Optimization.LinearProgramming.Geometry.SubspaceDecision

/-! The persistent minor service supplies the cumulative restart bound and one four-term
assignment realizing every completed price label of each uninterrupted learner epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract OracleSpec OracleSpec.MinorLog Matrix Recovery
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- All minor traffic of an arbitrary reachable word-level service path, including the
request causing each interruption. The two interfaces count exactly the same restarts. -/
theorem serveWord_traffic (S : Service D E) (ev : List (Recovery.Event Word)) (last : Contract.History ℚ)
    (h : Recovery.ServicePath S.serveWord [] ev last) :
    ∃ es : List (Index D E × Option ℚ), last=wireHistory es ∧ Follows S.oracle es ∧
      MinorLog.restartCount es=Recovery.restartCount ev ∧ es.length≤ev.length*(r*n) := by
  obtain ⟨fresh,sl⟩ := S.servicePath_slice h
  obtain ⟨es,wire⟩ := sl.named.events
  have lastEq : last=wireHistory es := by simpa only [sl.history,List.append_nil] using wire
  have legal := sl.matched (by trivial)
  refine ⟨es,lastEq,follows_of_answers es (lastEq ▸ legal),?_,?_⟩
  · rw [←wireCuts_history,←wire,sl.cuts]
  · have size := sl.size
    simpa only [wire,wireHistory,List.length_reverse,List.length_map] using size

/-- The continuing compression program pays for each accepted request and for the final
request in every interrupted price call. -/
theorem serveWord_serviceCost (S : Service D E) (ev : List (Recovery.Event Word)) (last : Contract.History ℚ)
    (h : Recovery.ServicePath S.serveWord [] ev last) :
    ∃ es : List (Index D E × Option ℚ), ∃ state cost, last=wireHistory es ∧
      ServiceTrace (fun u : Index D E => words u.val) S.program S.clock S.height S.outputBits S.ready es cost state ∧
      cost≤ev.length*(r*n)*S.clock ∧ MinorLog.restartCount es=Recovery.restartCount ev := by
  obtain ⟨es,wire,legal,cuts,count⟩ := S.serveWord_traffic ev last h
  obtain ⟨state,cost,trace,elapsed⟩ := legal.spec.1
  exact ⟨es,state,cost,wire,trace,elapsed.trans (Nat.mul_le_mul_right _ count),cuts⟩

theorem serveWord_restartCap (S : Service D E) (ev : List (Recovery.Event Word)) (last : Contract.History ℚ)
    (h : Recovery.ServicePath S.serveWord [] ev last) : Recovery.restartCount ev≤S.restartBudget := by
  obtain ⟨es,_,legal,cuts,_⟩ := S.serveWord_traffic ev last h
  exact cuts ▸ legal.spec.2.1

/-- Arbitrary earlier restarts and malformed learner words are permitted in `prior`.
Every observed label in this clean segment is evaluated against one full sealed assignment. -/
theorem serveWord_common (S : Service D E) (prior : List (Recovery.Event Word)) (start : Contract.History ℚ)
    (hp : Recovery.ServicePath S.serveWord [] prior start) (ev : List (Recovery.Event Word)) (last : Contract.History ℚ)
    (he : Recovery.ServicePath S.serveWord start ev last) (clean : Recovery.restartCount ev=0) :
    ∃ f : Compression.NonzeroPairMinor D E → ℚ, AdmissibleMinorAssignment D E (2^S.outputBits) f ∧
      ∀ (q : PriceGame.Query n) b,(priceQuery q.index q.prices,some b)∈ev → (geometricLabel D E q.prices q.index).eval f=b := by
  obtain ⟨old,oldShape,oldLegal,_,_⟩ := S.serveWord_traffic prior start hp
  obtain ⟨fresh,sl⟩ := S.servicePath_slice he
  have all := all_answers_of_no_wireCuts sl.named (sl.cuts.trans clean)
  obtain ⟨new,encoded⟩ := sl.named.answered_events all
  let rs : List (Index D E × Option ℚ) := new.map (fun e => (e.1,some e.2))
  have shape : last=wireHistory (old++rs) := by
    rw [sl.history,oldShape,encoded]
    simp [rs,wireHistory]
  have matched : answersMatch S.oracle last := sl.matched (by rw [oldShape]; exact oldLegal.answers)
  have follows := follows_of_answers (old++rs) (shape ▸ matched)
  obtain ⟨F,fit,mag,clipped⟩ := Follows.epoch old new follows
  have agrees : AgreesOnReplies D E fresh F := by
    rw [encoded]
    exact (agrees_wire_answers_iff new F).mpr fit
  refine ⟨fun u => F (interfaceIndex D E u), ⟨?_,fourLogAccuracy_of_sparse D E F clipped⟩,sl.labels F agrees⟩
  intro u
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using mag (interfaceIndex D E u)

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
