import OAI.Computability.VPVNP.PrimedCounterVisit

/-!
# Bounds on every executed prefix of node calls

The remaining node count drops by one at each successful visit. This makes
the terminal stack test redundant after exactly the prescribed number of calls.
Every histogram component can increase by at most the prefix length, including
prefixes of tapes that fail a later check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Fold

variable {n m s w : ℕ}

theorem visit_bounds (x : Fin m → Bool) (st out : VisitState n m s) (bs : List Bool)
    (hv : visit w x st bs = some out) :
    leafMass out.pending ≤ leafMass st.pending ∧
      pendingNodes out.pending + 1 = pendingNodes st.pending ∧
      ∀ a, out.counts a ≤ st.counts a + 1 := by
  rcases st with ⟨stack, marks, counts⟩
  cases stack with
  | nil => simp [visit] at hv
  | cons f stack =>
    cases ht : readToken w m s f.1.val bs with
    | none => simp [visit, ht] at hv
    | some t =>
      cases hstep : step x f t with
      | none => simp [visit, ht, hstep] at hv
      | some p =>
        obtain ⟨a, children⟩ := p
        cases hm : markToken marks t with
        | none => simp [visit, ht, hstep, hm] at hv
        | some next =>
          simp [visit, ht, hstep, hm] at hv
          subst out
          have hh := step_bounds x f t a children stack hstep
          refine ⟨hh.1, hh.2, fun b => ?_⟩
          classical
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          split <;> omega

/-- Run the chosen prefix without testing for end of traversal. -/
noncomputable def nodePrefix (w : ℕ) (x : Fin m → Bool) (st : VisitState n m s)
    (bs : List (List Bool)) := bs.foldlM (visit w x) st

theorem nodePrefix_bounds (x : Fin m → Bool) (st out : VisitState n m s) (bs : List (List Bool))
    (hr : nodePrefix w x st bs = some out) :
    leafMass out.pending ≤ leafMass st.pending ∧
      pendingNodes out.pending + bs.length = pendingNodes st.pending ∧
      ∀ a, out.counts a ≤ st.counts a + bs.length := by
  induction bs generalizing st with
  | nil => simp [nodePrefix] at hr; subst out; simp
  | cons b bs ih =>
    cases hv : visit w x st b with
    | none => simp [nodePrefix, hv] at hr
    | some next =>
      have htail : nodePrefix w x next bs = some out := by simpa [nodePrefix, hv] using hr
      obtain ⟨hm, hk, hc⟩ := visit_bounds x st next b hv
      obtain ⟨hm', hk', hc'⟩ := ih next htail
      refine ⟨hm'.trans hm, by simp only [List.length_cons]; omega, fun a => ?_⟩
      specialize hc a
      specialize hc' a
      simp only [List.length_cons]
      omega

/-- A full row has exactly as many node calls as pending nodes at its root. -/
theorem nodePrefix_visits (x : Fin m → Bool) (st : VisitState n m s) (bs : List (List Bool))
    (hl : bs.length = pendingNodes st.pending) :
    nodePrefix w x st bs = visits w x st bs := by
  induction bs generalizing st with
  | nil =>
    cases h : st.pending with
    | nil => simp [nodePrefix, visits, h]
    | cons f stack =>
      simp only [List.length_nil, h] at hl
      change 0 = 2 * f.1.val + 1 + pendingNodes stack at hl
      omega
  | cons b bs ih =>
    cases hv : visit w x st b with
    | none => simp [nodePrefix, visits, hv]
    | some next =>
      have hh := (visit_bounds x st next b hv).2.1
      simp only [List.length_cons] at hl
      simpa [nodePrefix, visits, hv] using ih next (by omega)

end PrimedCounter.Fold

end VPVNP
end Computability
end OAI
