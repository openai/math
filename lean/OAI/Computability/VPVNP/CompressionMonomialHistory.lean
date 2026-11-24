import OAI.Computability.VPVNP.NetworkMonomials
import OAI.Computability.VPVNP.CompressionBlock
import OAI.Computability.VPVNP.CompressionPowers

/-!
# Parameter labels through a compressor execution

All substeps of Section 7.4 use the same two sets of template labels. A
shrinking entry uses the first alphabet and a refresh entry the second.
The actual branch-dependent composition of passes preserves the witnesses
of every kernel, including through all repetitions of the fixed block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel.MonomialWitness

open Diagonal

variable {L M : Type} [Fintype L] [Fintype M] {A : Type*} [CommRing A] {x : A}

/-- Include the labels of a shrinking map in the common template alphabet. -/
def left (κ : L ⊕ M → A) (W : MonomialWitness (κ ∘ Sum.inl) x) : MonomialWitness κ x where
  Choice := W.Choice
  choiceFintype := W.choiceFintype
  exponents p := Sum.elim (W.exponents p) (fun _ ↦ 0)
  evaluates := by simpa [labelMonomial, Fintype.prod_sum_type, Function.comp_def] using W.evaluates

/-- Include the labels of a refresh map in the common template alphabet. -/
def right (κ : L ⊕ M → A) (W : MonomialWitness (κ ∘ Sum.inr) x) : MonomialWitness κ x where
  Choice := W.Choice
  choiceFintype := W.choiceFintype
  exponents p := Sum.elim (fun _ ↦ 0) (W.exponents p)
  evaluates := by simpa [labelMonomial, Fintype.prod_sum_type, Function.comp_def] using W.evaluates

end NetworkKernel.MonomialWitness

namespace Compression

open NetworkKernel

variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] {κ : Label → R}
variable {a b n g : ℕ} {X : State a g}

/-- Local entry witnesses for every kernel of a pass. -/
abbrev StatePass.MapWitnesses (p : StatePass R X b n) (κ : Label → R) :=
  ∀ i v old new, MonomialWitness κ ((p.step.term i).kernel v old new)

namespace StateExecution

/-- Witnesses along exactly the nodes reached by the chosen terms. -/
def MapWitnesses {a g : ℕ} {X : State a g} (κ : Label → R) : StateExecution R b n X → Type 1
  | .done _ => PUnit
  | .more p tail => p.MapWitnesses κ × ((i : p.step.Choice) → (tail i).MapWitnesses κ)

private def transportWitnesses {N M : Network} (e : N = M) (h : History R N)
    (W : h.KernelWitnesses κ) : (e ▸ h : History R M).KernelWitnesses κ := by
  subst M
  exact W

/-- Use the pass witnesses in the actual kernel history, respecting the
pass's equality of its selected output with the next state. -/
noncomputable def historyWitnesses (E : StateExecution R b n X) (W : E.MapWitnesses κ) :
    E.history.KernelWitnesses κ := by
  induction E with
  | done => exact PUnit.unit
  | more p tail ih => exact ⟨W.1, fun i ↦ transportWitnesses (p.output_eq i).symm _ (ih i (W.2 i))⟩

/-- Branch-dependent continuation uses the witnesses of both component
executions, without adding choices at their join. -/
def bindWitnesses {b' n' : ℕ} {a g : ℕ} {X : State a g} (E : StateExecution R b n X) :
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z)) → E.MapWitnesses κ →
      ((z : E.Choices) → (f z).MapWitnesses κ) → (E.bind f).MapWitnesses κ :=
  match E with
  | .done _ => fun _ _ after ↦ after ()
  | .more _ tail => fun f W after ↦ ⟨W.1, fun i ↦ (tail i).bindWitnesses
      (fun z ↦ f ⟨i,z⟩) (W.2 i) (fun z ↦ after ⟨i,z⟩)⟩

end StateExecution

namespace Procedure

variable {l p : ℕ} {μ : ℝ}

/-- A choice of local map witnesses for every input to a fixed procedure. -/
abbrev MapWitnesses (P : Procedure R a b l p μ) (κ : Label → R) :=
  ∀ g n h X, (P.run g n h X).MapWitnesses κ

namespace MapWitnesses

/-- The empty collection of local map-entry witnesses for the identity procedure, whose
execution ends at its input state. -/
def id (a : ℕ) (κ : Label → R) : (Procedure.id R a).MapWitnesses κ := by
  intro g n h X
  have hg : n = g := h.trans (Nat.zero_add g)
  subst g
  exact PUnit.unit

/-- Lift witnesses for every local map entry of a pass to the one-step procedure built from
that pass. -/
def ofPass {C : ℝ} (hp : 0 < p) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hcount : ∀ g X (i : (f g X).step.Choice), X.positions = p * ((f g X).next i).positions)
    (henergy : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + C * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ) :
        (Procedure.ofPass hp hμ hC f hcount henergy).MapWitnesses κ := by
  intro g n h X
  subst n
  exact ⟨W g X, fun _ ↦ PUnit.unit⟩

/-- Combine the first procedure's map-entry witnesses with those of the second procedure at the
final state of each first-stage branch. -/
def seq {c l' p' : ℕ} {ν : ℝ} {P : Procedure R a b l p μ} {Q : Procedure R b c l' p' ν}
    (W : P.MapWitnesses κ) (W' : Q.MapWitnesses κ) : (P.seq Q).MapWitnesses κ :=
  fun g n h X ↦
    let E := P.run (l' + g) n (h.trans (Nat.add_assoc l l' g)) X
    E.bindWitnesses (fun z ↦ Q.run g (l' + g) rfl (E.finalState z))
      (W _ _ _ X) (fun z ↦ W' _ _ _ (E.finalState z))

/-- Transport local map-entry witnesses along equalities of the procedure's degree, lane,
packing and energy parameters. -/
def reindex {a' b' l' p' : ℕ} {μ' : ℝ} {P : Procedure R a b l p μ} (W : P.MapWitnesses κ)
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hp : p = p'} {hμ : μ = μ'} :
    (P.reindex ha hb hl hp hμ).MapWitnesses κ := by
  subst a' b' l' p' μ'
  exact W

end MapWitnesses

/-- Repeating the block uses the original two label sets at every iteration. -/
def repeatWitnesses {P : Procedure R a a l p μ} (W : P.MapWitnesses κ) (g : ℕ) :
    (T n : ℕ) → (h : n = T * l + g) → (X : State a n) → (P.repeatExecution g T n h X).MapWitnesses κ
  | 0, n, h, X => MapWitnesses.id a κ g n (by simpa using h) X
  | t + 1, n, h, X =>
    let E := P.run (t * l + g) n (by rw [h, Nat.succ_mul]; omega) X
    E.bindWitnesses (fun z ↦ P.repeatExecution g t (t * l + g) rfl (E.finalState z))
      (W _ _ _ X) (fun z ↦ repeatWitnesses W g t _ rfl (E.finalState z))

end Procedure

namespace BlockSchedule

variable {k : Type*} [Field k] (S : BlockSchedule k)

private noncomputable def prefixWitnesses (shrink : S.ShrinkProcedures R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ) (j : ℕ) (hj : j ≤ S.steps) :
    (S.shrinkPrefix shrink j hj).MapWitnesses κ :=
  match j with
  | 0 => by
    rw [shrinkPrefix]
    exact (Procedure.MapWitnesses.id _ κ).reindex
  | j + 1 => by
    rw [shrinkPrefix]
    exact ((prefixWitnesses shrink W j (by omega)).seq (W ⟨j, hj⟩).reindex).reindex

/-- Preserve the concrete per-pass witnesses in the complete scheduled block. -/
noncomputable def assembleBlockWitnesses (shrink : S.ShrinkProcedures R)
    (refresh : S.RefreshProcedure R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ) (W' : refresh.MapWitnesses κ) :
    (S.assembleBlock shrink refresh).MapWitnesses κ := by
  unfold assembleBlock
  exact ((S.prefixWitnesses shrink W S.steps le_rfl).reindex.seq W').reindex

end BlockSchedule
end Compression

end VPVNP
end Computability
end OAI
