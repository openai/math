import OAI.Computability.VPVNP.PrimedCounterStackBounds

/-!
# Online traversal with a shared histogram

Each binary branch tape belongs to one node visit. The visit pops a frame,
decodes the choice at its actual degree, checks and sets the selected mark at
a leaf, pushes the ordered children and increments one shared production
counter. Successful traversals may start with arbitrary accumulated counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar

variable {n m s w : ℕ}

/-- Logical state for visiting grammar nodes one at a time while accumulating a production
histogram shared across sites. -/
structure VisitState (n m s : ℕ) where
  /-- Stack of grammar nodes awaiting visits, with the next node at the head. -/
  pending : List (Frame n (Fin s))
  /-- Terminal positions already used by the current site's parse. -/
  marked : Finset (Fin m)
  /-- Accumulated multiplicity of each production label from the nodes visited so far. -/
  counts : Label n m (Fin s) →₀ ℕ

/-- The one-bit mark memory accessed at a terminal. -/
def markToken (marked : Finset (Fin m)) : Token m (Fin s) → Option (Finset (Fin m))
  | .terminal j => if j ∈ marked then none else some (insert j marked)
  | .binary .. => some marked

/-- A single node call, including exactly one increment of the nominated
production's count. -/
noncomputable def visit (w : ℕ) (x : Fin m → Bool) (st : VisitState n m s) (bits : List Bool) :
    Option (VisitState n m s) := do
  let f :: rest := st.pending | none
  let t ← readToken w m s f.1.val bits
  let (a, children) ← step x f t
  let marked ← markToken st.marked t
  return ⟨children ++ rest, marked, st.counts + Finsupp.single a 1⟩

/-- Consume all node calls. The empty stack is required at completion. -/
noncomputable def visits (w : ℕ) (x : Fin m → Bool) :
    VisitState n m s → List (List Bool) → Option (VisitState n m s)
  | st, [] => if st.pending.isEmpty then some st else none
  | st, bits :: more => (visit w x st bits).bind (fun st' => visits w x st' more)

private theorem testMarks_cons (marked : Finset (Fin m)) (t : Token m (Fin s)) (ts : List (Token m (Fin s))) :
    testMarks marked (t::ts) = (markToken marked t).bind (fun next => testMarks next ts) := by
  cases t <;> simp [testMarks, markToken]
  split <;> rfl

/-- Online traversal produces the same labels and mark checks as the independent
stack and branch-stream decoders. Counts from preceding sites are retained. -/
theorem visits_eq (x : Fin m → Bool) (st : VisitState n m s) (bs : List (List Bool)) :
    visits w x st bs = (do
      let ts ← decodeVisits w x st.pending bs
      let marks ← testMarks st.marked ts
      let as ← scan x st.pending ts
      return ⟨[], marks, st.counts + tally as⟩) := by
  induction bs generalizing st with
  | nil =>
    obtain ⟨stack, marked, counts⟩ := st
    cases stack <;> simp [visits, decodeVisits, testMarks, scan, tally]
  | cons bits bs ih =>
    obtain ⟨stack, marked, counts⟩ := st
    cases stack with
    | nil => simp [visits, visit, decodeVisits]
    | cons f stack =>
      cases ht : readToken w m s f.1.val bits with
      | none => simp [visits, visit, decodeVisits, ht]
      | some t =>
        cases hs : step x f t with
        | none => simp [visits, visit, decodeVisits, ht, hs]
        | some val =>
          obtain ⟨a, cs⟩ := val
          cases hd : decodeVisits w x (cs ++ stack) bs with
          | none =>
            cases hm : markToken marked t <;> simp [visits, visit, decodeVisits, ht, hs, hm, ih, hd]
          | some ts =>
            cases hm : markToken marked t with
            | none => simp [visits, visit, decodeVisits, ht, hs, hm, hd, testMarks_cons]
            | some next =>
              cases hmarks : testMarks next ts <;> cases hscan : scan x (cs ++ stack) ts <;>
                simp [visits, visit, decodeVisits, ht, hs, hm, hd, ih, testMarks_cons, scan,
                  hmarks, hscan, tally, add_assoc]

/-- Accepted complete binary streams are exactly the streams of the parsimonious
local traversal, including all successful positions of every terminal. -/
theorem visits_accepts (x : Fin m → Bool) (d : Fin n) (root : Fin s)
    (counters : Label n m (Fin s) →₀ ℕ) (bs : List (List Bool))
    (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w) :
    (visits w x ⟨[(d,root)], ∅, counters⟩ bs).isSome ↔
      ∃ ts, decodeVisits w x [(d,root)] bs = some ts ∧ (positions ts).Nodup := by
  rw [visits_eq]
  cases hd : decodeVisits w x [(d,root)] bs with
  | none => simp
  | some ts =>
    have hsc := (decodeVisits_sound hm hs hn _ _ _ _ hd).2
    have hmarks := freshMarks_iff ts
    cases hs' : scan x [(d,root)] ts <;> cases hm' : testMarks ∅ ts <;> simp_all

/-- The updated shared counters after a single site equal its incoming counts
plus the production histogram from the actual binary trace. -/
theorem visits_counts (x : Fin m → Bool) (d : Fin n) (root : Fin s)
    (counters : Label n m (Fin s) →₀ ℕ) (b : SitePaths w x d root)
    (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w) :
    ∃ marks, visits w x ⟨[(d,root)], ∅, counters⟩ b.val =
      some ⟨[], marks, counters + siteHistogram hm hs hn x d root b⟩ := by
  rw [visits_eq]
  let ts := chosenTokens x d root b
  obtain ⟨hd, hmark⟩ := chosenTokens_spec x d root b
  obtain ⟨marks, hmarks⟩ := Option.isSome_iff_exists.mp ((freshMarks_iff ts).2 hmark)
  have hsc := (decodeVisits_sound hm hs hn _ _ _ _ hd).2
  refine ⟨marks, ?_⟩
  let as := (scan x [(d,root)] ts).get hsc
  have hs' : scan x [(d,root)] ts = some as := (Option.some_get hsc).symm
  change decodeVisits w x [(d,root)] b.val = some ts at hd
  change _ = some (VisitState.mk [] marks (counters + tally as))
  simp [hd, hmarks, hs']

end PrimedCounter

end VPVNP
end Computability
end OAI
