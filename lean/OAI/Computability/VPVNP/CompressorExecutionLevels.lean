import OAI.Computability.VPVNP.CursorDescriptorUnits

/-!
# Selected compressor levels for the descriptor passes

The labels in this file distinguish the scheduled six-party shrinking kernels
from the expander refresh kernel. Each label indexes the actual state pass of
the selected execution. Thus a native descriptor implementation may recover
the original input state and term index by cases on the label, including after
dependent sequencing and iteration.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open Compression
open PairSimulation.LocalHistory

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- Origin of a pass in the executable compression block. -/
inductive PassOrigin : {a g b n : ℕ} → {X : State a g} → StatePass R X b n → Type 1
  | shrink (i : Fin S.steps) {g n : ℕ}
      (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
      (X : State (S.degreeExponent i.castSucc) n) : PassOrigin (B.shrinkPassAt f hf i h X)
  | refresh {g : ℕ} (X : State S.portExponent (S.portExponent + g)) :
      PassOrigin (Refresh.dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
        (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
        (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2)

/-- Keep the origin of every elementary step, including on branch-dependent tails. -/
def PassOrigins {a g b n : ℕ} {X : State a g} : StateExecution R b n X → Type 1
  | .done _ => PUnit
  | .more p tail => PassOrigin B f hf p × ((i : p.step.Choice) → PassOrigins (tail i))

private def bindOrigins {a g b n b' n' : ℕ} {X : State a g} (E : StateExecution R b n X)
    (next : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (first : PassOrigins B f hf E) (rest : ∀ z, PassOrigins B f hf (next z)) :
    PassOrigins B f hf (E.bind next) := by
  induction E with
  | done => exact rest ()
  | more _ _ ih => exact ⟨first.1, fun i ↦ ih i _ (first.2 i) (fun z ↦ rest ⟨i,z⟩)⟩

variable {a b l d : ℕ} {μ : ℝ}

private abbrev ProcedureOrigins (P : Procedure R a b l d μ) :=
  ∀ g n h X, PassOrigins B f hf (P.run g n h X)

private def idOrigins (a : ℕ) : ProcedureOrigins B f hf (Procedure.id R a) := by
  intro g n h X
  have hn : n = g := h.trans (Nat.zero_add g)
  subst g
  exact PUnit.unit

private def passOriginsOfPass {C : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (p : ∀ g (X : State a (l+g)), StatePass R X b g)
    (hc : ∀ g X (i : (p g X).step.Choice), X.positions = d * ((p g X).next i).positions)
    (he : ∀ g X (i : (p g X).step.Choice),
      ((p g X).next i).energy ≤ μ * X.energy + C * (X.positions : ℝ)^2)
    (o : ∀ g X, PassOrigin B f hf (p g X)) : ProcedureOrigins B f hf (Procedure.ofPass hd hμ hC p hc he) := by
  intro g n h X
  subst n
  exact ⟨o g X, fun _ ↦ PUnit.unit⟩

private def ProcedureOrigins.seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ}
    {Q : Procedure R b c l' d' ν} (p : ProcedureOrigins B f hf P) (q : ProcedureOrigins B f hf Q) :
    ProcedureOrigins B f hf (P.seq Q) :=
  fun g n h X ↦
    let E := P.run (l'+g) n (h.trans (Nat.add_assoc l l' g)) X
    bindOrigins B f hf E _ (p _ _ _ X) (fun z ↦ q _ _ _ (E.finalState z))

private def ProcedureOrigins.reindex {a' b' l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ}
    (o : ProcedureOrigins B f hf P) {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'}
    {hμ : μ = ν} : ProcedureOrigins B f hf (P.reindex ha hb hl hd hμ) := by
  subst a' b' l' d' ν
  exact o

private noncomputable def shrinkOrigins (i : Fin S.steps) : ProcedureOrigins B f hf (B.shrinkProcedure f hf i) :=
  passOriginsOfPass B f hf _ _ _ _ _ _ (fun g X ↦ .shrink i (packingLaneBits_add _ g) X)

private noncomputable def refreshOrigins : ProcedureOrigins B f hf (B.refreshProcedure f hf) := by
  intro g n h X
  subst n
  exact ⟨.refresh X, fun _ ↦ PUnit.unit⟩

private noncomputable def prefixOrigins (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureOrigins B f hf (S.shrinkPrefix (B.shrinkProcedure f hf) j hj) :=
  match j with
  | 0 => by
    rw [BlockSchedule.shrinkPrefix]
    exact ProcedureOrigins.reindex B f hf (idOrigins B f hf _)
  | j + 1 => by
    rw [BlockSchedule.shrinkPrefix]
    exact ProcedureOrigins.reindex B f hf (ProcedureOrigins.seq B f hf (prefixOrigins j (by omega))
      (ProcedureOrigins.reindex B f hf (shrinkOrigins B f hf ⟨j,hj⟩)))

private noncomputable def blockOrigins : ProcedureOrigins B f hf (B.procedure f hf) := by
  unfold BlockSchedule.Templates.procedure BlockSchedule.assembleBlock
  exact ProcedureOrigins.reindex B f hf (ProcedureOrigins.seq B f hf
    (ProcedureOrigins.reindex B f hf (prefixOrigins B f hf S.steps le_rfl)) (refreshOrigins B f hf))

private noncomputable def repeatOrigins (g : ℕ) : (T n : ℕ) → (h : n = T*S.laneBits+g) →
    (X : State (S.degreeExponent 0) n) →
    PassOrigins B f hf ((B.procedure f hf).repeatExecution g T n h X)
  | 0, n, h, X => idOrigins B f hf _ g n (by simpa using h) X
  | t+1, n, h, X =>
    let E := (B.procedure f hf).run (t*S.laneBits+g) n (by rw [h, Nat.succ_mul]; omega) X
    bindOrigins B f hf E _ (blockOrigins B f hf _ _ _ X) (fun z ↦ repeatOrigins g t _ rfl (E.finalState z))

/-- Identify the actual kernel at every substep of the selected compression tree. -/
noncomputable def executeOrigins {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    PassOrigins B f hf (B.execute f hf T h X) :=
  repeatOrigins B f hf _ T n (Nat.add_sub_of_le h).symm X

/-- One concrete level with its input graph, selected term and selector encoding. -/
structure SelectedLevel where
  /-- Base-two exponent of the graph degree entering this selected pass. -/
  inputExponent : ℕ
  /-- Number of binary lane coordinates in the input state of the selected pass. -/
  inputLanes : ℕ
  /-- Base-two exponent of the graph degree produced by the selected pass. -/
  outputExponent : ℕ
  /-- Number of binary lane coordinates remaining in the output state of this pass. -/
  outputLanes : ℕ
  /-- Compression state on which the selected pass operates. -/
  input : State inputExponent inputLanes
  /-- State transition with the specified input state and output degree and lane dimensions. -/
  pass : StatePass R input outputExponent outputLanes
  /-- Witness identifying the pass as a particular scheduled shrink or refresh. -/
  origin : PassOrigin B f hf pass
  /-- Local kernel choice taken by this execution of the pass. -/
  term : pass.step.Choice
  /-- Boolean selector encoding of the chosen term for the native descriptor workers. -/
  selector : List Bool

namespace SelectedLevel

variable {B f hf}

/-- Charge counting one unit per input position and input slot, together with the selector
bits. -/
def units (v : SelectedLevel B f hf) : ℕ :=
  v.input.positions * (2 ^ v.inputExponent + 1) + v.selector.length

end SelectedLevel

private noncomputable def collectLevels {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses f) → ExecutionReaders E W →
      PassOrigins B f hf E → E.Choices → List (SelectedLevel B f hf)
  | .done _, _, _, _, _ => []
  | @StateExecution.more _ _ _ _ a g b' n' X p tail, W, r, o, z =>
    ⟨a,g,b',n',X,p,o.1,z.1,r.1.select.encode z.1⟩ :: collectLevels (tail z.1) (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2

private theorem collectLevels_sum_units {a g b n : ℕ} {X : State a g}
    (E : StateExecution R b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (o : PassOrigins B f hf E) (z : E.Choices) :
    ((collectLevels B f hf E W r o z).map SelectedLevel.units).sum = scanUnits E W r z := by
  induction E with
  | done => rfl
  | more p tail ih =>
    simp only [collectLevels, List.map_cons, List.sum_cons, scanUnits, SelectedLevel.units,
      ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2]

/-- Chronological list of the actual passes, input states, and selected terms along the given
block execution. -/
noncomputable def executeLevels {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) : List (SelectedLevel B f hf) :=
  collectLevels B f hf (B.execute f hf T h X) _
    (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X) (executeOrigins B f hf T h X) z

theorem executeLevels_sum_units {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T h X).Choices) :
    ((executeLevels B f hf T h X z).map SelectedLevel.units).sum =
      CursorNetwork.descriptorUnits B f hf T h X z :=
  collectLevels_sum_units B f hf _ _ _ _ _

end CompressorRecords

end

end VPVNP
end Computability
end OAI
