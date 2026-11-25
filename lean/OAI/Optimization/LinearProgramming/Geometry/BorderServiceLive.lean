import OAI.Optimization.LinearProgramming.Geometry.BorderServiceHistory

/-! Extend the running native service by one actual call at an arbitrary physical caller
history. Earlier calls determine the terminal native state, as well as their replies. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Contract OracleSpec OracleSpec.MinorLog Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

theorem ServiceTrace.append {ι : Type} {enc : ι → List ℕ} {p : Program} {c h w : ℕ}
    {initial middle final : State ℚ} {left right : List (ι × Option ℚ)} {a b : ℕ}
    (first : ServiceTrace enc p c h w initial left a middle) (second : ServiceTrace enc p c h w middle right b final) :
    ServiceTrace enc p c h w initial (left++right) (a+b) final := by
  induction first with
  | nil => simpa using second
  | cons tr pay exec last limit tag width tail ih =>
    simpa only [List.cons_append,Nat.add_assoc] using ServiceTrace.cons tr pay exec last limit tag width (ih second)

theorem height_of_call {p : Program} {clock H : ℕ} {s t : State ℚ}
    (h : call p clock H s t) : ∀i,ratBits (t.data i) ≤ H := by
  obtain ⟨k,_,tr,_,last,bits⟩ := h
  intro i
  exact last ▸ bits (Fin.last k) i

theorem ServiceTrace.height {ι : Type} {enc : ι → List ℕ} {p : Program} {clock H width cost : ℕ}
    {s t : State ℚ} {rs : List (ι × Option ℚ)} (h : ServiceTrace enc p clock H width s rs cost t)
    (initial : ∀i,ratBits (s.data i) ≤ H) : ∀i,ratBits (t.data i) ≤ H := by
  induction h with
  | nil => exact initial
  | cons tr pay core last bounds emitted small tail ih =>
    exact ih (fun i => last ▸ bounds _ i)

private theorem stopped {st : State ℚ} {q : Option ℚ} (h : emits st q) : ∃tag,st.output=some tag := by
  cases q with
  | none => exact ⟨1,h⟩
  | some _ => exact ⟨0,h.1⟩

/-- Fixing the earlier computed state does not restrict the service witness for an extended
request stream: terminal uniqueness aligns the old prefix state at every call. -/
private theorem advance_from_trace {ι : Type} {enc : ι → List ℕ} {p : Program} {c h w : ℕ}
    {initial middle : State ℚ} {left : List (ι × Option ℚ)} {cost : ℕ}
    (prior : ServiceTrace enc p c h w initial left cost middle) (u : ι) (a : Option ℚ)
    (full : Processes enc p c h w initial (left.map Prod.fst++[u]) (left++[(u,a)])) :
    ∃ last, call p (c-(enc u).length) h (resume middle (enc u)) last ∧ (enc u).length ≤ c ∧
      emits last a ∧ ∀q,a=some q → ratBits q ≤ w := by
  induction prior with
  | nil start =>
    cases full with
    | cons core len output width tail => exact ⟨_,core,len,output,width⟩
  | @cons start mid finish key ans tail k d tr pay first endState bound out val rest ih =>
    cases full with
    | cons another len altTag altWidth after =>
      have original : call p (c-(enc key).length) h (resume start (enc key)) mid := ⟨k,by omega,tr,first,endState,bound⟩
      obtain ⟨t,ht⟩ := stopped out
      obtain ⟨t',ht'⟩ := stopped altTag
      have same := call_terminal_unique original another ht ht'
      cases same
      exact ih after

@[simp] theorem pastRequests_cons_packet (u : Index D E) (response : List ℚ) (hist : Contract.History ℚ) :
    pastRequests D E ((packet u.val,response)::hist) = pastRequests D E hist ++ [u] := by
  simp [pastRequests,List.reverse_cons,List.filterMap_append]

namespace Service

/-- State of the unique ongoing service after the valid requests in the caller's current
history. The semantic construction of the oracle does not require the hardware to replay them. -/
def Live (S : Service D E) (hist : Contract.History ℚ) (z : State ℚ) : Prop :=
  ∃ cost,ServiceTrace (fun u : Index D E => words u.val) S.program S.clock S.height S.outputBits S.ready
    (S.events (pastRequests D E hist)) cost z

theorem live_initial (S : Service D E) : S.Live [] S.ready := by
  refine ⟨0,?_⟩
  rw [show pastRequests D E []=[] by rfl,S.events_nil]
  exact .nil S.ready

theorem Live.height {S : Service D E} {hist : Contract.History ℚ} {z : State ℚ}
    (live : S.Live hist z) (ready : ∀i,ratBits (S.ready.data i) ≤ S.height) : ∀i,ratBits (z.data i) ≤ S.height := by
  obtain ⟨_,trace⟩ := live
  exact trace.height ready

/-- The actual native starting memory for each next query, its exact returned value,
and the resulting persistent state are simultaneously identified. -/
theorem advance (S : Service D E) (hist : Contract.History ℚ) (state : State ℚ) (live : S.Live hist state) (u : Index D E) :
    ∃ ans next, S.oracle hist (packet u.val)=reply ans ∧
      call S.program (S.clock-(words u.val).length) S.height (resume state (words u.val)) next ∧
      emits next ans ∧ (∀ q,ans=some q → ratBits q ≤ S.outputBits) ∧
      S.Live ((packet u.val,reply ans)::hist) next := by
  let us := pastRequests D E hist
  let ans := S.next us u
  obtain ⟨c,prior⟩ := live
  have whole := (S.events_spec (us++[u])).1
  rw [(S.events_snoc us u).1] at whole
  have full : Processes (fun i : Index D E => words i.val) S.program S.clock S.height S.outputBits S.ready
      ((S.events us).map Prod.fst++[u]) (S.events us++[(u,ans)]) := by simpa only [S.requests] using whole
  obtain ⟨last,call,paid,emitted,small⟩ := advance_from_trace prior u ans full
  refine ⟨ans,last,S.oracle_packet u hist,call,emitted,small,?_⟩
  obtain ⟨k,hk,tr,core,endState,guard⟩ := call
  have once : ServiceTrace (fun i : Index D E => words i.val) S.program S.clock S.height S.outputBits state
      [(u,ans)] ((words u.val).length+k+0) last :=
    .cons tr (by omega) core endState guard emitted small (.nil _)
  refine ⟨c+((words u.val).length+k+0),?_⟩
  rw [pastRequests_cons_packet,(S.events_snoc _ _).1]
  exact prior.append once

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
