import OAI.Computability.VPVNP.CompressorExecutionLevels
import OAI.Computability.VPVNP.PairSimulationAssemblyBounds

/-!
# Identifying the actual local kernel reader at every recorded pass

The origin recorded by the online descriptor selects the very same shrink
or refresh term parser as the repeated monomial history, including its
kernel witnesses and all private choice words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression NetworkKernel CompressorRecords

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {a g b n : ℕ} {X : State a g}

/-- Recover the concrete local term parser indicated by the recorded
pass constructor, before any surrounding bind or repeat operation. -/
noncomputable def originReader {p : StatePass R X b n} (origin : PassOrigin B f hf p) :
    ∀ i, TermParsers f (p.step.term i) :=
  match origin with
  | .shrink j h Y => (shrinkPassReaders B f hf j h Y).termParsers
  | .refresh Y => ((refreshProcedureReaders B f hf _ _ rfl Y).1).termParsers

/-- Agreement holds for all choices of the local profile, including the
next pass selected by each possible continuation. -/
def ReaderOrigins {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (origins : PassOrigins B f hf E) : Prop :=
  match E with
  | .done _ => True
  | .more _ tail => (∀ i, r.1.termParsers i = originReader B f hf origins.1 i) ∧
      ∀ i, ReaderOrigins (tail i) (K.2 i) (r.2 i) (origins.2 i)

open private bindOrigins ProcedureOrigins idOrigins ProcedureOrigins.seq ProcedureOrigins.reindex
  shrinkOrigins refreshOrigins prefixOrigins blockOrigins repeatOrigins from OAI.Computability.VPVNP.CompressorExecutionLevels
open private prefixReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

private theorem bindMatch {b' n' : ℕ} (E : StateExecution R b n X)
    (next : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (K : E.MapWitnesses f) (V : ∀ z, (next z).MapWitnesses f)
    (r : ExecutionReaders E K) (s : ∀ z, ExecutionReaders (next z) (V z))
    (o : PassOrigins B f hf E) (t : ∀ z, PassOrigins B f hf (next z))
    (first : ReaderOrigins B f hf E K r o) (rest : ∀ z, ReaderOrigins B f hf (next z) (V z) (s z) (t z)) :
    ReaderOrigins B f hf (E.bind next) _ (bindReaders E next K V r s) (bindOrigins B f hf E next o t) := by
  induction E with
  | done => exact rest ()
  | more _ _ ih =>
    exact ⟨first.1,fun i => ih i _ (K.2 i) _ (r.2 i) _ (o.2 i) _ (first.2 i) (fun z => rest ⟨i,z⟩)⟩

variable {l d : ℕ} {μ : ℝ}

private abbrev ProcedureMatch {P : Procedure R a b l d μ} {K : P.MapWitnesses f}
    (r : ProcedureReaders P K) (o : ProcedureOrigins B f hf P) :=
  ∀ g n h X, ReaderOrigins B f hf (P.run g n h X) _ (r g n h X) (o g n h X)

private theorem matchId (a : ℕ) : ProcedureMatch B f hf (ProcedureReaders.id a f) (idOrigins B f hf a) := by
  intro g n h X
  have eqn := h.trans (Nat.zero_add g)
  subst g
  trivial

private theorem matchSeq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {K : P.MapWitnesses f} {V : Q.MapWitnesses f}
    {r : ProcedureReaders P K} {s : ProcedureReaders Q V}
    {o : ProcedureOrigins B f hf P} {t : ProcedureOrigins B f hf Q}
    (first : ProcedureMatch B f hf r o) (rest : ProcedureMatch B f hf s t) :
    ProcedureMatch B f hf (r.seq s) (ProcedureOrigins.seq B f hf o t) :=
  fun g n eqn X =>
    let E := P.run (l'+g) n (eqn.trans (Nat.add_assoc l l' g)) X
    bindMatch B f hf E _ _ _ _ _ _ _ (first _ _ _ X) (fun z => rest _ _ _ (E.finalState z))

private theorem matchReindex {a' b' l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ}
    {K : P.MapWitnesses f} {r : ProcedureReaders P K} {o : ProcedureOrigins B f hf P}
    (h : ProcedureMatch B f hf r o) {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hm : μ = ν} :
    ProcedureMatch B f hf (r.reindex (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hm))
      (ProcedureOrigins.reindex B f hf o) := by subst a' b' l' d' ν; exact h

private theorem shrinkMatch (j : Fin S.steps) :
    ProcedureMatch B f hf (shrinkProcedureReaders B f hf j) (shrinkOrigins B f hf j) := by
  intro g n h X
  subst n
  exact ⟨fun _ => rfl,fun _ => trivial⟩

private theorem refreshMatch :
    ProcedureMatch B f hf (refreshProcedureReaders B f hf) (refreshOrigins B f hf) := by
  intro g n h X
  subst n
  exact ⟨fun _ => rfl,fun _ => trivial⟩

private theorem prefixMatch (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureMatch B f hf (prefixReaders S (B.shrinkProcedure f hf) (B.shrinkProcedureWitnesses f hf)
      (shrinkProcedureReaders B f hf) j hj) (prefixOrigins B f hf j hj) := by
  induction j with
  | zero =>
    simp only [prefixReaders,prefixOrigins,prefixWitnesses,BlockSchedule.shrinkPrefix]
    exact matchReindex B f hf (matchId B f hf _)
  | succ j ih =>
    simp only [prefixReaders,prefixOrigins,prefixWitnesses,BlockSchedule.shrinkPrefix]
    exact matchReindex B f hf (matchSeq B f hf (ih (Nat.le_of_succ_le hj))
      (matchReindex B f hf (shrinkMatch B f hf ⟨j,hj⟩)))

private theorem blockMatch :
    ProcedureMatch B f hf (blockReaders B f hf) (blockOrigins B f hf) := by
  unfold blockReaders blockOrigins assembleReaders
  exact matchReindex B f hf (matchSeq B f hf (matchReindex B f hf (prefixMatch B f hf S.steps le_rfl))
    (refreshMatch B f hf))

private theorem repeatMatch (g T n : ℕ) (h : n = T*S.laneBits+g) (X : State (S.degreeExponent 0) n) :
    ReaderOrigins B f hf ((B.procedure f hf).repeatExecution g T n h X) _
      (repeatReaders (blockReaders B f hf) g T n h X) (repeatOrigins B f hf g T n h X) := by
  induction T generalizing n with
  | zero =>
    have eqn : n = g := by simpa using h
    subst g
    trivial
  | succ T ih =>
    let E := (B.procedure f hf).run (T*S.laneBits+g) n (by rw [h,Nat.succ_mul]; omega) X
    exact bindMatch B f hf E _ _ _ _ _ _ _ (blockMatch B f hf _ _ _ X) (fun z => ih _ rfl (E.finalState z))

/-- Matching the physical origin now rewrites the whole selected term parser
to the shrink or refresh implementation proved at that origin. -/
theorem execute_originReaders {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    ReaderOrigins B f hf (B.execute f hf T hT X) _
      (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le hT).symm X)
      (executeOrigins B f hf T hT X) :=
  repeatMatch B f hf _ T n (Nat.add_sub_of_le hT).symm X

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
