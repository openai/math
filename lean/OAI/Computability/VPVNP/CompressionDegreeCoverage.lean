import OAI.Computability.VPVNP.CompressionMonomialHistory
import OAI.Computability.VPVNP.CompressionBlockHistory
import OAI.Computability.VPVNP.CompressionPowerHistory

/-!
# Degrees of map witnesses throughout a compressor execution

The witnesses and records are indexed by the same pass and selected term.
The sum of the recorded map degrees at a site therefore bounds every local
choice there. This property is preserved by joining procedures, assembling
a scheduled block, and repeating it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}

/-- The joint degree of a chosen kernel monomial is bounded by the degrees
of all map occurrences at its output site. -/
def StatePass.DegreeCovered {a g b n : ℕ} {X : State a g} (p : StatePass R X b n)
    (W : p.MapWitnesses κ) (rec : p.Records) : Prop :=
  ∀ i v x z c, (∑ label, (W i v x z).exponents c label) ≤ ∑ j, (rec i v).degree j

/-- Degree coverage at every site in every branch-dependent substep. -/
def StateExecution.DegreeCovered {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → E.MapWitnesses κ → E.Records → Prop
  | .done _, _, _ => True
  | .more p tail, W, rec =>
    p.DegreeCovered W.1 rec.1 ∧ ∀ i, (tail i).DegreeCovered (W.2 i) (rec.2 i)

theorem StateExecution.degreeCovered_bind {a g b n b' n' : ℕ} {X : State a g}
    (E : StateExecution R b n X) (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (W : E.MapWitnesses κ) (V : ∀ z, (f z).MapWitnesses κ)
    (u : E.Records) (v : ∀ z, (f z).Records)
    (hu : E.DegreeCovered W u) (hv : ∀ z, (f z).DegreeCovered (V z) (v z)) :
    (E.bind f).DegreeCovered (E.bindWitnesses f W V) (E.bindRecords f u v) := by
  induction E with
  | done => exact hv ()
  | more p tail ih =>
    exact ⟨hu.1, fun i => ih i _ (W.2 i) _ (u.2 i) _ (hu.2 i) (fun z => hv ⟨i, z⟩)⟩

namespace Procedure

variable {a b l d C m : ℕ} {μ : ℝ}

/-- The same degree bound for every admissible input state of a procedure. -/
abbrev DegreeCovered {P : Procedure R a b l d μ} (W : P.MapWitnesses κ) (B : P.RecordBounds C m) :=
  ∀ g n h X, (P.run g n h X).DegreeCovered (W g n h X) (B.records g n h X)

namespace DegreeCovered

theorem id (a C : ℕ) (κ : L → R) :
    DegreeCovered (MapWitnesses.id a κ) (RecordBounds.id R a C) := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g
  trivial

theorem ofPass {A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ)
    (rec : ∀ g X, (f g X).Records) (hb : ∀ g X, (f g X).Bounded (rec g X) C)
    (hcov : ∀ g X, (f g X).DegreeCovered (W g X) (rec g X)) :
    DegreeCovered (MapWitnesses.ofPass hd hμ hA f hc he W)
      (RecordBounds.ofPass hd hμ hA f hc he rec hb) := by
  intro g n h X
  subst n
  exact ⟨hcov g X, fun _ => trivial⟩

theorem seq {c l' d' D n : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {W : P.MapWitnesses κ} {V : Q.MapWitnesses κ}
    {B : P.RecordBounds C m} {B' : Q.RecordBounds D n}
    (h : DegreeCovered W B) (h' : DegreeCovered V B') :
    DegreeCovered (W.seq V) (B.seq B') :=
  fun g n eqn X =>
    let E := P.run (l' + g) n (eqn.trans (Nat.add_assoc l l' g)) X
    E.degreeCovered_bind _ _ _ _ _ (h _ _ _ X) (fun z => h' _ _ _ (E.finalState z))

theorem mono {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    {B : P.RecordBounds C m} {D n : ℕ} (h : DegreeCovered W B) (hC : C ≤ D) (hm : m ≤ n) :
    DegreeCovered W (B.mono hC hm) := h

theorem reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    {B : P.RecordBounds C m} (h : DegreeCovered W B)
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    DegreeCovered (W.reindex (ha := ha) (hb := hb) (hl := hl) (hp := hd) (hμ := hμ)) B.reindex := by
  subst a' b' l' d' μ'
  exact h

end DegreeCovered

theorem repeat_degreeCovered {P : Procedure R a a l d μ} {W : P.MapWitnesses κ}
    {B : P.RecordBounds C m} (hc : DegreeCovered W B) (g T n : ℕ) (h : n = T * l + g)
    (X : State a n) :
    (P.repeatExecution g T n h X).DegreeCovered
      (repeatWitnesses W g T n h X) (repeatRecords B g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t * l + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact E.degreeCovered_bind _ _ _ _ _ (hc _ _ _ X) (fun z => ih _ rfl (E.finalState z))

end Procedure

namespace BlockSchedule

open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory
open private prefixRecordBounds from OAI.Computability.VPVNP.CompressionBlockHistory

variable {k : Type*} [Field k] (S : BlockSchedule k) {C : ℕ}

private theorem prefix_degreeCovered (shrink : S.ShrinkProcedures R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ)
    (B : ∀ i, (shrink i).RecordBounds C 1) (h : ∀ i, Procedure.DegreeCovered (W i) (B i))
    (j : ℕ) (hj : j ≤ S.steps) :
    Procedure.DegreeCovered (prefixWitnesses S shrink W j hj)
      (prefixRecordBounds S shrink B j hj) := by
  induction j with
  | zero =>
    simp only [prefixRecordBounds, prefixWitnesses, shrinkPrefix]
    exact (Procedure.DegreeCovered.id _ C κ).reindex
  | succ j ih =>
    simp only [prefixRecordBounds, prefixWitnesses, shrinkPrefix]
    exact (((ih (Nat.le_of_succ_le hj)).seq (h ⟨j, hj⟩).reindex).mono
      (max_le le_rfl le_rfl) le_rfl).reindex

/-- Every shrinking step and the final refresh retain their own degree records
when the block is run on an arbitrary state. -/
theorem assemble_degreeCovered (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R)
    {D : Fin S.steps → ℕ} (W : ∀ i, (shrink i).MapWitnesses κ) (V : refresh.MapWitnesses κ)
    (B : ∀ i, (shrink i).RecordBounds (D i) 1) (B' : refresh.RecordBounds C 1)
    (h : ∀ i, Procedure.DegreeCovered (W i) (B i)) (h' : Procedure.DegreeCovered V B') :
    Procedure.DegreeCovered (S.assembleBlockWitnesses shrink refresh W V)
      (S.assembleBlockRecords shrink refresh B B') := by
  unfold assembleBlockWitnesses assembleBlockRecords
  apply Procedure.DegreeCovered.reindex
  apply Procedure.DegreeCovered.seq _ h'
  apply Procedure.DegreeCovered.reindex
  exact prefix_degreeCovered S shrink W _ (fun i => h i) S.steps le_rfl

end BlockSchedule
end Compression

end VPVNP
end Computability
end OAI
