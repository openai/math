import OAI.Optimization.LinearProgramming.Geometry.BorderService

/-! A scalar-oracle view of the persistent online compressor. Actual scalar exchanges
recover the same unique typed replies, restarting epochs, and common clipped assignment. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Contract OracleSpec OracleSpec.MinorLog RAM Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

theorem packet_injective : Function.Injective (fun u : Index D E => packet u.val) := by
  intro a b eq
  apply Subtype.ext
  apply words_injective
  exact (List.map_injective_iff.mpr (Nat.cast_injective (R := ℚ))) eq

theorem reply_injective : Function.Injective reply := by
  rintro (_ | q) (_ | v) h <;> simp_all [reply]

noncomputable def decode (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (message : List ℚ) : Option (Index D E) := by
  classical
  exact if h : ∃ u : Index D E, packet u.val=message then some h.choose else none

@[simp] theorem decode_packet (u : Index D E) : decode D E (packet u.val)=some u := by
  have h : ∃ v : Index D E, packet v.val=packet u.val := ⟨u,rfl⟩
  rw [decode,dite_eq_left h]
  exact congrArg some (packet_injective h.choose_spec)

/-- Public scalar history is newest first. Only canonical minor requests advance this
particular service; the geometric caller sends exactly those packets. -/
noncomputable def pastRequests (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (h : Contract.History ℚ) : List (Index D E) := h.reverse.filterMap fun e => decode D E e.1

def wireEvent (e : Index D E × Option ℚ) : List ℚ × List ℚ := (packet e.1.val,reply e.2)

def wireHistory (events : List (Index D E × Option ℚ)) : Contract.History ℚ := (events.map wireEvent).reverse

@[simp] theorem wireHistory_snoc (events : List (Index D E × Option ℚ)) (u : Index D E) (ans : Option ℚ) :
    wireHistory (events++[(u,ans)])=(packet u.val,reply ans)::wireHistory events := by
  simp [wireHistory,wireEvent]

@[simp] theorem pastRequests_wire (events : List (Index D E × Option ℚ)) :
    pastRequests D E (wireHistory events)=events.map Prod.fst := by
  unfold pastRequests wireHistory
  simp only [List.reverse_reverse]
  induction events with
  | nil => rfl
  | cons x xs ih => simp [wireEvent,ih]

namespace Service

/-- The same deterministic service seen through the scalar-oracle interface. For ill-formed
packets the total interface returns the restart encoding. -/
noncomputable def oracle (S : Service D E) : ScalarOracle ℚ := fun h msg =>
  match decode D E msg with
  | none => reply none
  | some u => reply (S.next (pastRequests D E h) u)

@[simp] theorem oracle_packet (S : Service D E) (u : Index D E) (h : Contract.History ℚ) :
    S.oracle h (packet u.val)=reply (S.next (pastRequests D E h) u) := by simp [oracle]

theorem responds (S : Service D E) : ∀ (hist : Contract.History ℚ) (u : Index D E), ∃ ans : Option ℚ,
    S.oracle hist (packet u.val)=reply ans ∧ ∀ q,ans=some q → ratBits q ≤ S.outputBits := by
  intro h u
  exact ⟨_,S.oracle_packet u h,(S.events_snoc (pastRequests D E h) u).2⟩

end Service

/-- A physical scalar-oracle interaction restricted to typed, correctly encoded minor calls,
with each answer obtained at the actual history accumulated so far. -/
inductive Follows (o : ScalarOracle ℚ) : List (Index D E × Option ℚ) → Prop where
  | nil : Follows o []
  | append {events : List (Index D E × Option ℚ)} (u : Index D E) (ans : Option ℚ)
      (prior : Follows o events) (returned : o (wireHistory events) (packet u.val)=reply ans) :
      Follows o (events++[(u,ans)])

theorem Follows.events {S : Service D E} {xs : List (Index D E × Option ℚ)}
    (h : Follows S.oracle xs) : S.events (xs.map Prod.fst)=xs := by
  induction h with
  | nil => exact S.events_nil
  | @append xs u ans _ hx ih =>
    have eq : S.next (xs.map Prod.fst) u=ans := reply_injective (by simpa only [S.oracle_packet,pastRequests_wire] using hx)
    simp only [List.map_append,List.map_cons,List.map_nil]
    rw [(S.events_snoc _ _).1,ih,eq]

/-- Every actual interaction has one continuing physical service state throughout, the sealed
cumulative restart allowance, and the required simultaneous four-term assignment at each prefix. -/
theorem Follows.spec {S : Service D E} {xs : List (Index D E × Option ℚ)} (h : Follows S.oracle xs) :
    (∃ t cost, ServiceTrace (fun u : Index D E => words u.val) S.program S.clock S.height S.outputBits S.ready xs cost t ∧
      cost ≤ xs.length*S.clock) ∧
    restartCount xs ≤ S.restartBudget ∧
    ∀ j ≤ xs.length, extension n S.outputBits (logarithm D E) (xs.take j) := by
  obtain ⟨run,cap,extend⟩ := S.events_spec (xs.map Prod.fst)
  rw [h.events] at run cap extend
  obtain ⟨t,c,trace,bound⟩ := trace_of_processes run
  exact ⟨⟨t,c,trace,by simpa using bound⟩,cap,extend⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
