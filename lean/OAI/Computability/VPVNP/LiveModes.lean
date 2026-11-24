import OAI.Computability.VPVNP.EvaluatorTail
import OAI.Computability.VPVNP.ExponentTrace
import OAI.Computability.VPVNP.Diagonal

/-!
# First-half and tail paths in the live chain

For fixed primed exterior bits, nominations, and pair paths, each first-half
group checks its incoming and outgoing counters. The middle cut initializes
the evaluator. Each tail group checks a single transition and the uniquely
encoded outgoing configuration. Forgetting these forced fields leaves just
one accepting path of the evaluator on the full sum of the exponents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveChain

open CutSchedule ExponentTrace UniversalMachine

variable {h Δ t Z csize : ℕ}

/-- There are `2^h - 1` cuts strictly after the midpoint and before the final
endpoint. On each of these the tail sends an evaluator configuration. -/
abbrev TailBits (h Δ : ℕ) :=
  (j : Fin (2 ^ h - 1)) → Bits (width (h + 1) Δ (2 ^ h + (j.val + 1)))

private def layout (hfit : 1 + csize ≤ Δ) (j : Fin (2 ^ h - 1)) :=
  tailLayout h Δ (2 ^ h + (j.val + 1)) csize (by omega)
    (by rw [pow_succ]; have := j.isLt; omega) hfit

private def timeAfter (j : Fin (2 ^ h - 1)) : Fin (2 ^ h + 1) :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

/-- Every outgoing tail cut encodes the configuration reached after the
corresponding transition and contains only zero padding. -/
def TailValid (hfit : 1 + csize ≤ Δ) (E : Program) (encode : EvaluatorTail.State E.extra → Bits csize)
    (states : Fin (2 ^ h + 1) → EvaluatorTail.State E.extra) (bits : TailBits h Δ) : Prop :=
  ∀ j, layout hfit j (bits j) = (true, encode (states (timeAfter j)), fun _ => false)

theorem tailBits_unique (hfit : 1 + csize ≤ Δ) (E : Program)
    (encode : EvaluatorTail.State E.extra → Bits csize)
    (states : Fin (2 ^ h + 1) → EvaluatorTail.State E.extra) :
    ∃! bits, TailValid hfit E encode states bits := by
  refine ⟨fun j => (layout hfit j).symm (true, encode (states (timeAfter j)), fun _ => false),
    fun j => (layout hfit j).apply_symm_apply _, ?_⟩
  intro bits hb
  exact funext fun j => (layout hfit j).eq_symm_apply.mpr (hb j)

/-- One set of local paths with their constrained first-half bit fields,
their branch-distinguished tail history, and their serialized tail cuts. -/
abbrev LocalRun (hfit : 1 + t * Z ≤ Δ) (hconfig : 1 + csize ≤ Δ)
    (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ) (E : Program)
    (initial : (Fin t → ℕ) → Config E.extra) (encode : EvaluatorTail.State E.extra → Bits csize) :=
  (live : {bits : LiveBits h Δ // Valid hfit ξ inc bits}) ×
    (trace : EvaluatorTail.Traces E (2 ^ h)
      (initial (fun a => (counters hfit live.val (Fin.last (2 ^ h)) a).val))) ×
    {bits : TailBits h Δ // TailValid hconfig E encode trace.2.val bits}

/-- A fixed collection of pair choices has one canonically filled first half,
then exactly as many completions as the evaluator has accepting paths. -/
noncomputable def localRunEquiv (hfit : 1 + t * Z ≤ Δ) (hconfig : 1 + csize ≤ Δ)
    (ξ : Exterior h Δ) (inc : Fin (2 ^ h) → Fin t → ℕ)
    (hbound : ∀ (i : Fin (2 ^ h)) a, partialSum inc i.succ a < 2 ^ Z) (E : Program)
    (initial : (Fin t → ℕ) → Config E.extra) (encode : EvaluatorTail.State E.extra → Bits csize) :
    LocalRun hfit hconfig ξ inc E initial encode ≃
      Fin (paths E (2 ^ h) (initial (fun a => ∑ i, inc i a))) := by
  let first := {bits : LiveBits h Δ // Valid hfit ξ inc bits}
  let liveDefault : Unique first := ((unique_subtype_iff_existsUnique _).mpr (existsUnique_live hfit ξ inc hbound)).some
  let initialAt (live : first) := initial (fun a => (counters hfit live.val (Fin.last (2 ^ h)) a).val)
  let hist (live : first) := EvaluatorTail.Traces E (2 ^ h) (initialAt live)
  let tail (live : first) (tr : hist live) := {bits : TailBits h Δ //
    TailValid hconfig E encode tr.2.val bits}
  let tailDefault (live : first) (tr : hist live) : Unique (tail live tr) :=
    ((unique_subtype_iff_existsUnique _).mpr (tailBits_unique hconfig E encode tr.2.val)).some
  let initialConfig := initial (fun a => ∑ i, inc i a)
  have init_eq (live : first) : initialAt live = initialConfig :=
    congrArg initial (funext (middle_counters hfit ξ inc live.val live.property))
  let stripTail (live : first) : ((tr : hist live) × tail live tr) ≃ hist live :=
    Equiv.sigmaUnique _ _
  let stripFirst : ((live : first) × hist live) ≃ hist (default : first) := Equiv.uniqueSigma _
  let tailPaths := EvaluatorTail.tracesEquiv E (2 ^ h) initialConfig
  let choices := {w : Fin (2 ^ h) → Bool // acceptsChoices E (2 ^ h) initialConfig w}
  have hc : Fintype.card choices = paths E (2 ^ h) initialConfig := by
    rw [paths_eq_card_choices, Fintype.card_subtype]
  let last : hist (default : first) ≃ Fin (paths E (2 ^ h) initialConfig) :=
    (Equiv.cast (congrArg (EvaluatorTail.Traces E (2 ^ h)) (init_eq default))).trans
      (tailPaths.symm.trans (Fintype.equivFinOfCardEq hc))
  exact ((Equiv.sigmaCongrRight stripTail).trans stripFirst).trans last

/-- Applying the local path bijection at every nomination gives the exact
two-mode path type of Proposition 9.1. -/
noncomputable def liveModesEquiv {Nom : Type*} {Path : Exterior h Δ → Fin (2 ^ h) → Nom → Type*}
    (hfit : 1 + t * Z ≤ Δ) (hconfig : 1 + csize ≤ Δ) (E : Program)
    (initial : (Fin t → ℕ) → Config E.extra) (encode : EvaluatorTail.State E.extra → Bits csize)
    (inc : ∀ ξ (μ : Fin (2 ^ h) → Nom), ((i : Fin (2 ^ h)) → Path ξ i (μ i)) →
      Fin (2 ^ h) → Fin t → ℕ)
    (hbound : ∀ ξ μ q (i : Fin (2 ^ h)) a, partialSum (inc ξ μ q) i.succ a < 2 ^ Z) :
    (Unit ⊕ ((ξ : Exterior h Δ) × (μ : Fin (2 ^ h) → Nom) ×
      (q : (i : Fin (2 ^ h)) → Path ξ i (μ i)) ×
      LocalRun hfit hconfig ξ (inc ξ μ q) E initial encode)) ≃
    Diagonal.LiveModes (fun ξ μ q => paths E (2 ^ h) (initial (fun a => ∑ i, inc ξ μ q i a))) :=
  (Equiv.refl Unit).sumCongr <| Equiv.sigmaCongrRight fun ξ => Equiv.sigmaCongrRight fun μ =>
    Equiv.sigmaCongrRight fun q =>
      localRunEquiv hfit hconfig ξ (inc ξ μ q) (hbound ξ μ q) E initial encode

end LiveChain

end VPVNP
end Computability
end OAI
