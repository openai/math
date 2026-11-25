import OAI.Optimization.LinearProgramming.Geometry.WirePredicates
import OAI.Optimization.LinearProgramming.Geometry.BorderServiceRuns

/-! Converting actual physical packets into the chronological typed history consumed
by the independently specified persistent online-compression machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec BorderBatch

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- Each legal physical history admits a sequence of named service requests and their
actual optional answers. Reversal accounts for the RAM's newest-first history. -/
theorem NamedTraffic.events {hist : Contract.History ℚ} (traffic : NamedTraffic D E hist) :
    ∃ es : List (MinorLog.Index D E × Option ℚ), hist=wireHistory es := by
  induction hist with
  | nil => exact ⟨[],rfl⟩
  | cons w tail ih =>
    obtain ⟨es,he⟩ := ih (fun t ht => traffic t (List.mem_cons_of_mem _ ht))
    obtain ⟨u,hu,replyForm⟩ := traffic w List.mem_cons_self
    have existsAns : ∃ ans : Option ℚ, w.2=reply ans := by
      rcases replyForm with stop|⟨v,valid⟩
      · exact ⟨none,stop⟩
      · exact ⟨some v,valid⟩
    obtain ⟨ans,ha⟩ := existsAns
    refine ⟨es++[(u,ans)],?_⟩
    rw [wireHistory_snoc,←he]
    exact congrArg (fun b => b::tail) (Prod.ext hu ha)

/-- Apply the external service's deterministic request semantics directly to the
traffic of a real machine run; no per-packet transition witnesses are given. -/
theorem NamedTraffic.follows_physical {p : OracleProgram} {o : ScalarOracle ℚ}
    {initial final : Config ℚ} {k : ℕ} (traffic : NamedTraffic D E final.history)
    (run : OracleRun p o initial k final) (prior : answersMatch o initial.history) :
    ∃ es : List (MinorLog.Index D E × Option ℚ), final.history=wireHistory es ∧ Follows o es := by
  obtain ⟨es,wire⟩ := traffic.events
  exact ⟨es,wire,follows_of_physical_run run prior es wire⟩

/-- A success-only scalar exchange specifies numeric answers for a chronological
list of sealed minor requests. -/
theorem NamedTraffic.answered_events {hist : Contract.History ℚ} (traffic : NamedTraffic D E hist)
    (success : ∀ w ∈ hist, ∃ v, w.2=[0,v]) :
    ∃ es : List (MinorLog.Index D E × ℚ), hist=wireHistory (es.map (fun e => (e.1,some e.2))) := by
  induction hist with
  | nil => exact ⟨[],rfl⟩
  | cons w tail ih =>
    obtain ⟨es,he⟩ := ih (fun t ht => traffic t (List.mem_cons_of_mem _ ht))
      (fun t ht => success t (List.mem_cons_of_mem _ ht))
    obtain ⟨u,hu,_⟩ := traffic w List.mem_cons_self
    obtain ⟨v,hv⟩ := success w List.mem_cons_self
    refine ⟨es++[(u,v)],?_⟩
    simp only [List.map_append,List.map_cons,List.map_nil,wireHistory_snoc,←he]
    exact congrArg (fun b => b::tail) (Prod.ext hu hv)

private theorem agrees_history (es : List (MinorLog.Index D E × ℚ)) (F : MinorLog.Index D E → ℚ)
    (known : ∀ e ∈ es, F e.1=e.2) : AgreesOnReplies D E (wireHistory (es.map (fun e => (e.1,some e.2)))) F := by
  intro u v h
  simp only [wireHistory,List.map_map,List.mem_reverse,List.mem_map] at h
  obtain ⟨e,he,wire⟩ := h
  change (packet e.1.val,[0,e.2])=(packet u.val,[0,v]) at wire
  have hu : e.1=u := packet_injective (congrArg Prod.fst wire)
  have hv : e.2=v := by simpa using congrArg Prod.snd wire
  simpa [hu,hv] using known e he

/-- A completed sequence of calls to an actual persistent service has a common
clipped assignment for every geometrical price query in the sequence. -/
theorem NamedTraffic.service_epoch (S : Service D E) {p : OracleProgram} {initial final : Config ℚ}
    {k : ℕ} (run : OracleRun p S.oracle initial k final) (prior : answersMatch S.oracle initial.history)
    (traffic : NamedTraffic D E final.history) (success : ∀ w ∈ final.history, ∃ v, w.2=[0,v]) :
    ∃ F : MinorLog.Index D E → ℚ, AgreesOnReplies D E final.history F ∧
      (∀ u, |(F u : ℝ)|≤(2:ℝ)^S.outputBits) ∧
      ∀ a : MinorLog.Index D E →₀ ℤ, a.sum (fun _ c => c.natAbs)≤4 →
        |MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c:ℝ)*(F u:ℝ))) -
          MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c:ℝ)*MinorLog.logarithm D E u))|≤
            (1/2:ℝ)^(MinorLog.threshold n) := by
  obtain ⟨es,wire⟩ := traffic.answered_events success
  have follows := follows_of_physical_run run prior _ wire
  obtain ⟨F,ans,mag,clip⟩ := Follows.epoch [] es (by simpa using follows)
  exact ⟨F,by rw [wire]; exact agrees_history es F ans,mag,clip⟩

/-- The same extension holds for a success-only suffix following an arbitrary earlier
service history, including previous restarts. Thus the label calls of one epoch share
one four-term clipped assignment even when they used different prices. -/
theorem NamedTraffic.service_epoch_after (S : Service D E) {p : OracleProgram} {initial final : Config ℚ}
    {k : ℕ} (run : OracleRun p S.oracle initial k final) (matched : answersMatch S.oracle initial.history)
    (old : List (MinorLog.Index D E × Option ℚ)) (recent : Contract.History ℚ)
    (shape : final.history=recent++wireHistory old) (traffic : NamedTraffic D E recent)
    (success : ∀ w ∈ recent, ∃ v, w.2=[0,v]) :
    ∃ F : MinorLog.Index D E → ℚ, AgreesOnReplies D E recent F ∧
      (∀ u, |(F u : ℝ)|≤(2:ℝ)^S.outputBits) ∧
      ∀ a : MinorLog.Index D E →₀ ℤ, a.sum (fun _ c => c.natAbs)≤4 →
        |MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c:ℝ)*(F u:ℝ))) -
          MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c:ℝ)*MinorLog.logarithm D E u))|≤
            (1/2:ℝ)^(MinorLog.threshold n) := by
  obtain ⟨es,wire⟩ := traffic.answered_events success
  have whole : final.history=wireHistory (old++es.map (fun e => (e.1,some e.2))) := by
    rw [shape,wire]
    simp [wireHistory]
  have follows := follows_of_physical_run run matched _ whole
  obtain ⟨F,ans,mag,clip⟩ := Follows.epoch old es follows
  exact ⟨F,by rw [wire]; exact agrees_history es F ans,mag,clip⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
