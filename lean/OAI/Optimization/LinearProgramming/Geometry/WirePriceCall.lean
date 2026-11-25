import OAI.Optimization.LinearProgramming.Geometry.WirePriceSlice
import OAI.Optimization.LinearProgramming.Geometry.WordService
import OAI.Optimization.LinearProgramming.Geometry.PriceStepNamed

/-! The response to each literal learner packet has a correctly charged segment of
persistent minor history. Rejected minor requests contribute exactly one outer restart. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract OracleSpec OracleSpec.MinorLog Matrix Recovery
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

private theorem successWords_eq {κ : Type*} (packet : κ → List ℚ) (xs : List (κ × ℚ)) (old : Contract.History ℚ) :
    MinorQuery.answeredWords packet xs old = PivotPrefixRAM.answeredHistory packet xs old := rfl

private theorem priceSlice (S : Service D E) (before : Contract.History ℚ) (w : Word) (q : PriceGame.Query n)
    (read : Contraction.BisectionRAM.readQuery n w=some q) :
    ∃ fresh, WordSlice S [(w,(S.priceStep before q).1)] before (S.priceStep before q).2 fresh := by
  obtain ⟨xs,out,run,returned,capacity,keys,stop⟩ := S.priceStep_decompose before q
  have matched (h : answersMatch S.oracle before) : answersMatch S.oracle (MinorQuery.recorded (keyPacket D E) xs out before) := by
    rw [←show (S.priceStep before q).2 = MinorQuery.recorded (keyPacket D E) xs out before from congrArg Prod.snd returned]
    exact S.priceTrace_answers before q h
  rw [returned]
  refine ⟨MinorQuery.recorded (keyPacket D E) xs out [],MinorQuery.recorded_append ..,?_,matched,?_,?_,?_⟩
  · cases out with
    | inr b => exact named_answeredWords xs keys
    | inl k =>
      intro e he
      rcases List.mem_cons.mp he with rfl|tail
      · obtain ⟨u,hu⟩ := stop
        exact ⟨interfaceIndex D E u,by simp [keyPacket,hu,packet],Or.inl rfl⟩
      · exact named_answeredWords xs keys e tail
  · cases out <;> simp [MinorQuery.recorded,successWords_eq,reply,wireCuts_answeredWords,Recovery.restartCount]
  · cases out <;> simpa [MinorQuery.recorded,MinorQuery.answeredWords,MinorQuery.restartCost,Nat.add_comm] using capacity
  · intro F agrees p b member
    cases out with
    | inl k => simp at member
    | inr v =>
      have eq : (priceQuery p.index p.prices,some b)=(w,some v) := by simpa only [List.mem_singleton,Sum.elim_inr] using member
      have same : p=q := Option.some.inj ((Contraction.BisectionRAM.readQuery_price p).symm.trans
        ((congrArg (Contraction.BisectionRAM.readQuery n) (congrArg Prod.fst eq)).trans read))
      have hb : b=v := Option.some.inj (congrArg Prod.snd eq)
      subst p; subst b
      have extend := minor_values_of_agrees xs keys F agrees
      exact (geometricLabel_eval D E _ q.prices q.index).trans (run.eval_of_extends _ extend)

private theorem toReply_inj {a b : Option Bool} {x y : Contract.History ℚ} (h : toReply a x=toReply b y) :
    a=b ∧ x=y := by cases a <;> cases b <;> simp_all [toReply]

/-- The harmless totalization on malformed words preserves the minor state. On every
canonical price word the returned bit and the complete response history are reproduced. -/
theorem word_step_slice (S : Service D E) (before : Contract.History ℚ) (w : Word) (ans : Option Bool)
    (after : Contract.History ℚ) (e : S.serveWord before w=toReply ans after) :
    ∃ fresh, WordSlice S [(w,ans)] before after fresh := by
  cases read : Contraction.BisectionRAM.readQuery n w with
  | none =>
    have both := toReply_inj (a:=some false) (x:=before) (by simpa only [serveWord,read,toReply] using e)
    obtain ⟨eq,rfl⟩ := both
    rw [←eq]
    refine ⟨[],rfl,fun _ no => (List.not_mem_nil no).elim,id,by rfl,by simp,?_⟩
    intro _ _ q b mem
    have word : priceQuery q.index q.prices=w := congrArg Prod.fst (List.mem_singleton.mp mem)
    rw [←word,Contraction.BisectionRAM.readQuery_price q] at read
    contradiction
  | some q =>
    have both := toReply_inj (by simpa only [serveWord,read] using e)
    simpa only [both.1,both.2] using priceSlice S before w q read

/-- Accumulate all actual answered or interrupted price words and discard none of their
physical minor calls. The scalar suffix is prepended in the reverse chronological order. -/
theorem servicePath_slice (S : Service D E) {before after : Contract.History ℚ} {events : List (Recovery.Event Word)}
    (h : Recovery.ServicePath S.serveWord before events after) :
    ∃ fresh, WordSlice S events before after fresh := by
  induction h with
  | nil state => exact ⟨[],WordSlice.nil S state⟩
  | @answer st st' last w b log e _ ih =>
    obtain ⟨a,head⟩ := S.word_step_slice st w (some b) st' e
    obtain ⟨b,tail⟩ := ih
    exact ⟨b++a,head.append tail⟩
  | @restart st st' last w log e _ ih =>
    obtain ⟨a,head⟩ := S.word_step_slice st w none st' e
    obtain ⟨b,tail⟩ := ih
    exact ⟨b++a,head.append tail⟩

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
