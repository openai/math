import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetTotal

/-! # Common width budgets for the physical phases of a CRT batch

The phases can have different inputs and commands. They share the outer width
used to price the enclosing sweep, and good widths recover the maximum of the
individual phase clocks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask
open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax

/-- A named, effectively generated phase with unconditional execution and a
sharper bound on the same command for successful candidates. -/
structure WidthPhase {P : Type} [Primcodable P] {I : P → Type} (good : P → Prop)
    (cut : P → ℕ) (width : ∀ p, I p → ℕ) (u v : ∀ p, I p → Tree) (target : P → ℕ → ℕ) where
  inCap : P → ℕ → ℕ
  outCap : P → ℕ → ℕ
  input : ∀ p i, (u p i).count ≤ inCap p (width p i)
  output : ∀ p i, (v p i).count ≤ outCap p (width p i)
  cmd : P → Cmd
  R : ℕ
  effective : Effective ltr cmd
  positive : 0 < R
  within : ∀ p, Within R (cmd p)
  total : ∀ p i, ∃ t, ∀ env r, Fits env (cmd p) (pile 0 (u p i) r) (pile 0 (v p i) r) t
  fast : ∀ p, good p → Runs (cmd p)
    (fun i : {i : I p // cut p ≤ width p i} => target p (width p i.val))
    (fun i => width p i.val) (fun i => u p i.val) (fun i => v p i.val)

namespace WidthPhase

variable {P : Type} [Primcodable P] {good : P → Prop} {cut : P → ℕ}

/-- Convert the execution and size estimates of one phase to width-only
budgets on all candidates. -/
theorem budgets {I : P → Type} {width : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    {target : P → ℕ → ℕ} (phase : WidthPhase good cut width u v target) :
    ∃ arena clock : P → ℕ → ℕ,
      Family (fun p i => clock p (width p i)) (fun p i => arena p (width p i)) u v ∧
      (∀ p w, w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p, good p → ∀ w ≥ cut p, arena p w = w ∧ clock p w = max w (target p w) :=
  total_width_budgets good cut width u v phase.inCap phase.outCap target phase.input phase.output
    phase.cmd phase.R phase.effective phase.positive phase.within phase.total phase.fast

/-- Use a common arena and clock for every named phase, retaining the maximum
of their individual clocks above the good candidate's cutoff. -/
theorem common {Q : Type} [Fintype Q] {I : Q → P → Type} {width : ∀ q p, I q p → ℕ}
    {u v : ∀ q p, I q p → Tree} {target : Q → P → ℕ → ℕ}
    (phases : ∀ q, WidthPhase good cut (width q) (u q) (v q) (target q)) :
    ∃ arena clock : P → ℕ → ℕ,
      (∀ q, Family (fun p i => clock p (width q p i)) (fun p i => arena p (width q p i)) (u q) (v q)) ∧
      (∀ p w, w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p, good p → ∀ w ≥ cut p,
        arena p w = w ∧ clock p w = max w (Finset.univ.sup (fun q => target q p w)) := by
  classical
  choose S T run bounds sharp using fun q => (phases q).budgets
  let maxAt (h : Q → P → ℕ → ℕ) (p : P) (w : ℕ) := max w (Finset.univ.sup (fun q => h q p w))
  have each (h : Q → P → ℕ → ℕ) (q : Q) (p : P) (w : ℕ) : h q p w ≤ maxAt h p w :=
    (Finset.le_sup (f := fun q => h q p w) (Finset.mem_univ q)).trans (le_max_right ..)
  refine ⟨maxAt S,maxAt T,fun q => (run q).mono (fun p i => each T q p _) (fun p i => each S q p _),
    fun p w => ⟨le_max_left ..,?_⟩,fun p ok w hw => ⟨?_,?_⟩⟩
  · exact max_le (le_max_left ..) (Finset.sup_le fun q _ => ((bounds q p w).2).trans (each T q p w))
  · exact le_antisymm (max_le le_rfl (Finset.sup_le fun q _ => (sharp q p ok w hw).1.le)) (le_max_left ..)
  · apply le_antisymm
    · refine max_le (le_max_left ..) (Finset.sup_le fun q _ => ?_)
      rw [(sharp q p ok w hw).2]
      exact max_le (le_max_left ..) (each target q p w)
    · refine max_le (le_max_left ..) (Finset.sup_le fun q _ => ?_)
      exact (le_max_right w (target q p w)).trans ((sharp q p ok w hw).2.ge.trans (each T q p w))

/-- A forward placement, an inverse placement, and a grouped mask on a common
outer index set receive the same measurements. -/
theorem three {I : P → Type} {width : ∀ p, I p → ℕ}
    {u₀ u₁ u₂ v₀ v₁ v₂ : ∀ p, I p → Tree} {t₀ t₁ t₂ : P → ℕ → ℕ}
    (f : WidthPhase good cut width u₀ v₀ t₀) (b : WidthPhase good cut width u₁ v₁ t₁)
    (m : WidthPhase good cut width u₂ v₂ t₂) :
    ∃ arena clock : P → ℕ → ℕ,
      Family (fun p i => clock p (width p i)) (fun p i => arena p (width p i)) u₀ v₀ ∧
      Family (fun p i => clock p (width p i)) (fun p i => arena p (width p i)) u₁ v₁ ∧
      Family (fun p i => clock p (width p i)) (fun p i => arena p (width p i)) u₂ v₂ ∧
      (∀ p w, w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p, good p → ∀ w ≥ cut p,
        arena p w = w ∧ clock p w = max w (max (t₀ p w) (max (t₁ p w) (t₂ p w))) := by
  classical
  let u : Fin 3 → ∀ p, I p → Tree := ![u₀,u₁,u₂]
  let v : Fin 3 → ∀ p, I p → Tree := ![v₀,v₁,v₂]
  let t : Fin 3 → P → ℕ → ℕ := ![t₀,t₁,t₂]
  have phases (q : Fin 3) : WidthPhase good cut width (u q) (v q) (t q) := by
    refine Fin.cases f (fun r => ?_) q
    refine Fin.cases b (fun s => ?_) r
    exact Fin.cases m (fun z => Fin.elim0 z) s
  obtain ⟨S,T,run,bounds,fast⟩ := common phases
  refine ⟨S,T,run 0,run 1,run 2,bounds,fun p ok w hw => ⟨(fast p ok w hw).1,?_⟩⟩
  rw [(fast p ok w hw).2,show (Finset.univ : Finset (Fin 3)) = {0,1,2} by decide,
    Finset.sup_insert,Finset.sup_insert,Finset.sup_singleton]
  rfl

end WidthPhase
end EffectiveBoundedTask

end NearSquareRoot
end Computability
end OAI
