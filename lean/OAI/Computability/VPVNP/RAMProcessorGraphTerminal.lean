import OAI.Computability.VPVNP.RAMProcessorPrelude
import OAI.Computability.VPVNP.StructuredStackTotal
import OAI.Computability.VPVNP.StructuredStackCount

/-!
# Rejecting halts in the compiled site processor

A failed format, credit, or consistency check can halt inside an embedded routine.
Its literal rejecting row survives compilation of the graph and attachment of the
site prelude. Its path contributes zero and stops within one tick of reaching that row,
for every continuation of the enclosing program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

variable {K Q J : Type} [DecidableEq K]

/-- A literal rejecting halt in the routine's own control space. The endpoint
has a named instruction so that it still halts when the routine is linked. -/
def Routine.Rejects (rt : Routine K Q) (t : ℕ) (s : Stacks K) : Prop :=
  ∃ q u, StackRuns rt.standalone t (some rt.entry) s (some q) u ∧ rt.code q = .halt false

/-- A deterministic path into a rejecting row stops, independently of every
normal-return continuation. -/
theorem Routine.Rejects.verdict {rt : Routine K Q} {n : ℕ} {s : Stacks K}
    (h : rt.Rejects n s) (c : ℕ → Stacks K → ℕ) (d : ℕ → Stacks K → Prop) (fuel : ℕ) :
    rt.count c (fuel+n+1) s = 0 ∧ rt.AllStops d (fuel+n+1) s := by
  obtain ⟨z,u,hr,bad⟩ := h
  have walk {n q s j u} (run : StackRuns rt.standalone n q s j u) :
      ∀ z, j = some z → rt.code z = .halt false →
      rt.countFrom c (fuel+n+1) q s = 0 ∧ rt.AllStopsFrom d (fuel+n+1) q s := by
    induction run with
    | nil =>
      rintro z rfl hb
      simp [countFrom, AllStopsFrom, hb]
    | @cons q s _ _ _ _ n step _ ih =>
      intro z hz hb
      have tail := ih z hz hb
      cases q with
      | none => cases step <;> contradiction
      | some q =>
        rw [show fuel+(n+1)+1=(fuel+n+1)+1 by omega]
        cases step with
        | push he | pop he | goto he =>
          change rt.code q = _ at he
          simpa only [countFrom, AllStopsFrom, he] using tail
  exact walk hr z rfl bad

/-- A normal first return enters a second routine's literal rejecting row. -/
theorem Routine.Runs.then_reject {a : Routine K Q} {b : Routine K J} {t n : ℕ}
    {s mid : Stacks K} (ha : a.Runs t s mid) (hb : b.Rejects n mid) :
    (a.followedBy b).Rejects (t+n) s := by
  obtain ⟨z,u,hr,bad⟩ := hb
  let outer := a.followedBy b
  let labels (q : Option J) : Option (Q ⊕ J) := q.elim none (some ∘ Sum.inr)
  have hc (q : Option J) (h : (b.standalone q).returns = false) :
      outer.standalone (labels q) = (b.standalone q).rename id labels := by
    cases q with | none => contradiction | some q => rfl
  have htail := hr.lift id Function.injective_id labels s hc
  have same (x : Stacks K) : installStacks id s x = x := by
    funext i; exact installStacks_at Function.injective_id s x i
  rw [same, same] at htail
  refine ⟨.inr z, u, (ha.link outer Sum.inl (some (.inr b.entry)) (fun _ ↦ rfl)).trans htail, ?_⟩
  simp [Routine.followedBy, Routine.install, bad, StackOp.rename]

/-- The normal labels of the input code must be accepting halts. This makes
every literal rejecting row of the source an interior row of the compiled routine. -/
theorem FiniteRoutine.reject_ofStackCode [Fintype Q] {src : StackCode K Q} {normal : Q → Bool}
    {entry : Q} (he : normal entry = false) (haccept : ∀ q, normal q = true → src q = .halt true)
    {n : ℕ} {s : Stacks K} (h : RejectRun src n entry s) :
    (ofStackCode src id entry normal).body.Rejects n s := by
  obtain ⟨z,u,hr,bad⟩ := h
  let rt := (ofStackCode src id entry normal).body
  let labels (q : Q) := if normal q then none else some q
  have hc (q : Q) (h : (src q).returns = false) :
      rt.standalone (labels q) = (src q).rename id labels := by
    have hn : normal q = false := by
      cases hx : normal q with
      | false => rfl
      | true => rw [haccept q hx] at h; contradiction
    simp [rt, ofStackCode, ofRoutine, Routine.standalone, Routine.close, labels, hn]
  have hrun := hr.lift id Function.injective_id labels s hc
  have same (x : Stacks K) : installStacks id s x = x := by
    funext i; exact installStacks_at Function.injective_id s x i
  have hz : normal z = false := by
    cases hx : normal z with
    | false => rfl
    | true => have hh := haccept z hx; rw [bad] at hh; cases hh
  rw [same, same] at hrun
  refine ⟨z,u,?_,?_⟩
  · change StackRuns rt.standalone n (some entry) s (some z) u
    simp only [labels, he, hz, Bool.false_eq_true, ↓reduceIte] at hrun
    exact hrun
  · simp [ofStackCode, ofRoutine, hz, bad, StackOp.rename]

namespace SiteProcessor

open BurstRAM PrivateRAM

variable {p r k : ℕ}

/-- The named rejected row of the complete burst graph is also a rejecting
row in the corresponding finite routine. -/
theorem graphRoutine_reject (T : Template p r k) {n : ℕ} {s : Stacks (Port r k)}
    (h : RejectRun (table T) n (atLabel T .initialRecord) s) :
    (graphRoutine T).body.Rejects n s :=
  FiniteRoutine.reject_ofStackCode (normal := graphDone) rfl (graphDone_row T) h

/-- Include the boot steps that allocate and stage the physical record fields. -/
theorem callSite_reject (T : Template p r k) {m n : ℕ} {bare start : Stacks (Port r k)}
    (booted : boot.Runs m bare start) (h : RejectRun (table T) n (atLabel T .initialRecord) start) :
    (callSite T).body.Rejects (m+n) bare :=
  booted.then_reject (graphRoutine_reject T h)

/-- A failed call-site run has count zero under every continuation and a uniform
stopping bound, including the final instruction that observes the rejecting halt. -/
theorem callSite_reject_verdict (T : Template p r k) {m n : ℕ} {bare start : Stacks (Port r k)}
    (booted : boot.Runs m bare start) (h : RejectRun (table T) n (atLabel T .initialRecord) start)
    (c : ℕ → Stacks (Port r k) → ℕ) (d : ℕ → Stacks (Port r k) → Prop) (extra : ℕ) :
    (callSite T).body.count c (extra+(m+n)+1) bare = 0 ∧
      (callSite T).body.AllStops d (extra+(m+n)+1) bare :=
  (callSite_reject T booted h).verdict c d extra

end SiteProcessor
end RAMTape

end VPVNP
end Computability
end OAI
