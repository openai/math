import OAI.Computability.VPVNP.CompressorExecutionLevels

/-! # The block calendar of the actual mathematical compression execution

The initial cursor network undergoes shrinking at indices zero through
the last shrinking index, followed by one refresh, on every completed block.
Dependent bind and the intermediate degree casts preserve the chronological
order. The schedule also identifies the active pass before choosing a term,
which matters when that selector has no admitted term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ExecutionCalendar
open Compression
open private bindOrigins ProcedureOrigins idOrigins ProcedureOrigins.seq ProcedureOrigins.reindex
  shrinkOrigins refreshOrigins prefixOrigins blockOrigins repeatOrigins from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- Calendar label for an indexed shrinking pass or the subsequent degree refresh. -/
inductive Phase where
  | shrink (index : ℕ)
  | refresh
  deriving DecidableEq

/-- Read the calendar label from the origin of a concrete state pass. -/
def kind {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} : PassOrigin B f hf p → Phase
  | .shrink i _ _ => .shrink i.val
  | .refresh _ => .refresh

/-- Follow the prescribed schedule on every choice, including the next
row's phase on branches for which no later full path exists. -/
def Follows {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → PassOrigins B f hf E → List Phase → Prop
  | .done _, _, phases => phases = []
  | .more _ _, _, [] => False
  | .more _ tail, origin, s::ss => kind origin.1 = s ∧ ∀ i, Follows (tail i) (origin.2 i) ss

private theorem bind {a g b n b' n' : ℕ} {X : State a g} (E : StateExecution R b n X)
    (tail : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (o : PassOrigins B f hf E) (ot : ∀ z, PassOrigins B f hf (tail z))
    (ss ts : List Phase) (first : Follows E o ss) (rest : ∀ z, Follows (tail z) (ot z) ts) :
    Follows (E.bind tail) (bindOrigins B f hf E tail o ot) (ss++ts) := by
  induction E generalizing ss with
  | done =>
    change ss = [] at first
    subst ss
    exact rest ()
  | more p next ih =>
    cases ss with
    | nil => exact first.elim
    | cons s ss => exact ⟨first.1,fun i => ih i _ (o.2 i) _ ss (first.2 i) (fun z => rest ⟨i,z⟩)⟩

variable {a b l d : ℕ} {μ : ℝ}

private abbrev ProcedureFollows {P : Procedure R a b l d μ}
    (o : ProcedureOrigins B f hf P) (ss : List Phase) : Prop :=
  ∀ g n h X, Follows (P.run g n h X) (o g n h X) ss

private theorem seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {p : ProcedureOrigins B f hf P} {q : ProcedureOrigins B f hf Q} {ss ts : List Phase}
    (first : ProcedureFollows p ss) (next : ProcedureFollows q ts) :
    ProcedureFollows (ProcedureOrigins.seq B f hf p q) (ss++ts) := by
  intro g n h X
  exact bind _ _ _ _ _ _ (first _ _ _ X) (fun z => next _ _ _ _)

private theorem reindex {a' b' l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {o : ProcedureOrigins B f hf P}
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = ν}
    {ss : List Phase} (h : ProcedureFollows o ss) :
    ProcedureFollows (ProcedureOrigins.reindex B f hf o (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hμ)) ss := by
  subst a' b' l' d' ν
  exact h

private theorem id (a : ℕ) : ProcedureFollows (idOrigins B f hf a) [] := by
  intro g n h X
  have hn : n = g := h.trans (Nat.zero_add g)
  subst g
  rfl

private theorem shrinking (i : Fin S.steps) : ProcedureFollows (shrinkOrigins B f hf i) [.shrink i.val] := by
  intro g n h X
  subst n
  exact ⟨rfl,fun _ => rfl⟩

private theorem refreshing : ProcedureFollows (refreshOrigins B f hf) [.refresh] := by
  intro g n h X
  subst n
  exact ⟨rfl,fun _ => rfl⟩

private theorem prefix_order (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureFollows (prefixOrigins B f hf j hj) ((List.range j).map Phase.shrink) := by
  induction j with
  | zero =>
    simp only [prefixOrigins,BlockSchedule.shrinkPrefix,List.range_zero,List.map_nil]
    exact reindex (id _)
  | succ j ih =>
    simp only [prefixOrigins,BlockSchedule.shrinkPrefix,List.range_succ,List.map_append,List.map_singleton]
    exact reindex (seq (ih (Nat.le_of_succ_le hj)) (reindex (shrinking ⟨j,hj⟩)))

/-- Chronological pass labels of one compressor block, with each shrink in order followed by
refresh. -/
def oneBlock (steps : ℕ) := (List.range steps).map Phase.shrink ++ [.refresh]

private theorem block : ProcedureFollows (blockOrigins B f hf) (oneBlock S.steps) := by
  unfold blockOrigins oneBlock
  exact reindex (seq (reindex (prefix_order S.steps le_rfl)) refreshing)

/-- Calendar obtained by concatenating the pass lists of the requested number of complete
blocks. -/
def blocks (steps t : ℕ) := (List.replicate t (oneBlock steps)).flatten

private theorem repeats (g T n : ℕ) (h : n = T * S.laneBits + g) (X : State (S.degreeExponent 0) n) :
    Follows ((B.procedure f hf).repeatExecution g T n h X) (repeatOrigins B f hf g T n h X) (blocks S.steps T) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    rfl
  | succ t ih =>
    let E := (B.procedure f hf).run (t*S.laneBits+g) n (by rw [h,Nat.succ_mul]; omega) X
    exact bind E _ _ _ (oneBlock S.steps) (blocks S.steps t) (block _ _ _ X) (fun z => ih _ rfl (E.finalState z))

/-- The selected compressor's mathematical tree follows precisely the
finite block program's repeating shrinking and refresh schedule. -/
theorem execute_follows (T : ℕ) {n : ℕ} (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    Follows (B.execute f hf T h X) (executeOrigins B f hf T h X) (blocks S.steps T) :=
  repeats _ _ _ _ _

end CompressorRecords.ExecutionCalendar

end VPVNP
end Computability
end OAI
