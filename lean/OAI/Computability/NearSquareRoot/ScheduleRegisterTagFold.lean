import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterLookup
import OAI.Computability.NearSquareRoot.KernelSelectorAlign
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Emitting the fold over an arity-dependent alphabet and state set -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTagFold
open IntegerMultiplication Code CommonRegisters GeneratorSyntax RegisterWitness EffectiveTask

/-- Tape program of P192's left fold. The callback operates on a letter and one
state, both at the top of the caller's stack. -/
def command (c : Cmd) :=
  splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie (Task.sweepBody c)))

theorem within {R : ℕ} (hR : 3 ≤ R) (c : Cmd) (hc : Within R c) : Within R (command c) := by
  simp [command,Within,move,forward,forwardBody,flood,give,pack,RegisterLookup.sweepBody_within hR,hc]
  omega

theorem effective {P : Type} [Primcodable P] {c : P → Cmd} (h : Effective ltr c) :
    Effective ltr (fun p => command (c p)) := by
  have sw : Effective ltr (fun p => Task.sweepBody (c p)) :=
    KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
      ((effective_const _ _).join ((effective_const _ _).join (h.join (effective_const _ _))))
  exact KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
    ((effective_const _ _).join sw.tie)

theorem run {A S : Type} (input : A → Tree) (state : S → Tree) (step : S → A → S) (c : Cmd)
    (h : Runs c (fun _ : A × S => 0) (fun u => (input u.1).fork (state u.2))
      (fun u => state (step u.2 u.1))) :
    Runs (command c) (fun u : List A × S => (Task.forest input u.1).count)
      (fun u => (Task.forest input u.1).fork (state u.2)) (fun u => state (u.1.foldl step u.2)) := by
  let U := {p : A × S × Unit // True}
  let V := {p : List A × S × Unit // ∀ x ∈ p.1, True}
  let coords (p : U) := (p.val.1,p.val.2.1)
  let idx (p : List A × S) : V := ⟨(p.1,p.2,()),by simp⟩
  have scan : Runs (command c) (fun p : V => costSum (fun _ : A => 0) p.val.1+(Task.forest input p.val.1).count)
      (fun p => (Task.forest input p.val.1).fork (state p.val.2.1))
      (fun p => state (p.val.1.foldl step p.val.2.1)) :=
    command_contract (command c) from Task.foldLeft (Y := Unit) (fun _ => input)
      (fun _ => state) (fun _ => step) (fun _ _ => 0) (D := fun _ _ => True) ⟨c,h.on coords⟩
  have zero (l : List A) : costSum (fun _ : A => 0) l = 0 := by induction l <;> simp_all
  exact (scan.on idx).conform (fun p => by simp [idx,zero]) (fun _ => rfl) (fun _ => rfl)

/-- The fixed empty tally is appended as a seed to a serialized input tree. -/
def seed := ((give 0 false).join (pack 0)).join
  (splitRoot 0 (fun _ => .pass) ((move 0 1 2).join ((move 0 3 2).join
    ((move 1 0 2).join ((move 3 0 2).join (pack 0))))))

private theorem seed_run : Runs seed Tree.count id (fun t => t.fork (.atom false)) := by
  let nil : Tree := .atom false
  have s : Runs ((give 0 false).join (pack 0)) (fun _ : Tree => 0) id (fun x => nil.fork x) :=
    command_contract ((give 0 false).join (pack 0)) from Task.supply nil (id (α := Tree))
  let c : Cmd := splitRoot 0 (fun _ => .pass) ((move 0 1 2).join ((move 0 3 2).join
    ((move 1 0 2).join ((move 3 0 2).join (pack 0)))))
  have ex : Runs c (fun x => nil.count+x.count) (fun x => nil.fork x) (fun x => x.fork nil) :=
    command_contract c from Task.exchange (fun _ : Tree => nil) id
  have se := s.comp ex
  -- The source command records both named phases.
  change Runs _ _ _ _ at se
  exact se.bound 2 (fun x => by change 0+(1+x.count)+1 ≤ 2*(x.count+1); omega)

/-- Compile an input-dependent finite-state scan on aligned address columns. The
machine receives only the encoded column list. The table seed is the empty tally. -/
theorem aligned {P : Type} [Primcodable P] (a : P → ℕ) (S : P → Type)
    (state : ∀ p, S p → Tree) (init : ∀ p, S p) (next : ∀ p, S p → KernelSelectorAlign.Column (a p) → S p)
    (out : ∀ p, S p → Tree) (zero : ∀ p, state p (init p) = .atom false) :
    ∀ᶠ R : ℕ in Filter.atTop,
      Family R (fun p (_ : KernelSelectorAlign.Column (a p) × S p) => 0)
        (fun p u => (send u.1).fork (state p u.2)) (fun p u => state p (next p u.2 u.1)) →
      Family R (fun p (_ : S p) => 0) state out →
      Family R (fun p (l : List (KernelSelectorAlign.Column (a p))) => l.length)
        (fun _ l => send l) (fun p l => out p (l.foldl (next p) (init p))) := by
  filter_upwards [Filter.eventually_ge_atTop 3,RegisterSelect.within_eventually seed] with R hR hs
  rintro ⟨tick,eff,ht⟩ ⟨fin,effFin,hf⟩
  refine ⟨fun p => (seed.join (command (tick p))).join (fin p),
    ((effective_const ltr seed).join (effective eff)).join effFin,fun p => ?_⟩
  obtain ⟨w,step⟩ := ht p
  obtain ⟨wf,finish⟩ := hf p
  refine ⟨⟨⟨hs,within hR _ w⟩,wf⟩,?_⟩
  let A := KernelSelectorAlign.Column (a p)
  let prep (l : List A) : List A × S p := (l,init p)
  have start := (seed_run.on (send (X := List A))).conform (fun _ => rfl) (fun _ => rfl)
    (fun l => by change (send l).fork (.atom false) = (Task.forest send l).fork (state p (init p))
                 rw [Task.forest_send,zero])
  have scan := (run send (state p) (next p) (tick p) step).on prep
  have tail := finish.on (fun l : List A => l.foldl (next p) (init p))
  apply ((start.comp scan).comp tail).bound (4*a p+8)
  intro l
  change (send l).count+(Task.forest send l).count+0+1 ≤ _
  rw [Task.forest_send]
  change size l + size l + 0 + 1 ≤ _
  rw [KernelSelectorAlign.columns_size]
  ring_nf
  omega

end RegisterTagFold

end NearSquareRoot
end Computability
end OAI
