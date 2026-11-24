import OAI.Computability.VPVNP.CompressorExecutionLevels

/-!
# Order of the selected compressor levels

The native calendar repeats a fixed list of pass types. Choices alter the
data of the next level but preserve the scheduled order. The first indices
in a block enumerate shrinking transitions in increasing order, and the
last index is its refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open Compression PairSimulation.LocalHistory
open private bindOrigins ProcedureOrigins idOrigins passOriginsOfPass shrinkOrigins refreshOrigins
  prefixOrigins blockOrigins repeatOrigins collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open private ProcedureOrigins.seq ProcedureOrigins.reindex from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- Slot of the elementary kernel in one block of the online calendar. -/
def PassOrigin.ordinal {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} :
    PassOrigin B f hf p → ℕ
  | .shrink i .. => i.val
  | .refresh .. => S.steps

private def OrderMatches {a g b n : ℕ} {X : State a g} : (E : StateExecution R b n X) →
    PassOrigins B f hf E → List ℕ → Prop
  | .done _, _, js => js = []
  | .more _ tail, o, js => ∃ rest, js = o.1.ordinal :: rest ∧ ∀ i, OrderMatches (tail i) (o.2 i) rest

private theorem order_bind {a g b n b' n' : ℕ} {X : State a g} (E : StateExecution R b n X)
    (next : (z : E.Choices) → StateExecution R b' n' (E.finalState z)) (o : PassOrigins B f hf E)
    (after : ∀ z, PassOrigins B f hf (next z)) {js ks : List ℕ}
    (h : OrderMatches E o js) (h' : ∀ z, OrderMatches (next z) (after z) ks) :
    OrderMatches (E.bind next) (bindOrigins B f hf E next o after) (js++ks) := by
  induction E generalizing js with
  | done => change js = [] at h; subst js; exact h' ()
  | more p tail ih =>
    obtain ⟨t,rfl,ht⟩ := h
    exact ⟨t++ks,rfl,fun i ↦ ih i _ (o.2 i) _ (ht i) (fun z ↦ h' ⟨i,z⟩)⟩

variable {a b l d : ℕ} {μ : ℝ}

private abbrev ProcedureOrder {P : Procedure R a b l d μ} (o : ProcedureOrigins B f hf P) (js : List ℕ) :=
  ∀ g n h X, OrderMatches (P.run g n h X) (o g n h X) js

private theorem order_id (a : ℕ) : ProcedureOrder (idOrigins B f hf a) [] := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g; rfl

private theorem order_seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {o : ProcedureOrigins B f hf P} {p : ProcedureOrigins B f hf Q} {js ks : List ℕ}
    (ho : ProcedureOrder o js) (hp : ProcedureOrder p ks) : ProcedureOrder (ProcedureOrigins.seq B f hf o p) (js++ks) :=
  fun g n h X ↦
    let E := P.run (l'+g) n (h.trans (Nat.add_assoc l l' g)) X
    order_bind E _ _ _ (ho _ _ _ X) (fun z ↦ hp _ _ _ (E.finalState z))

private theorem order_reindex {a' b' l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ}
    {o : ProcedureOrigins B f hf P} {js : List ℕ} (ho : ProcedureOrder o js)
    {ha : a=a'} {hb : b=b'} {hl : l=l'} {hd : d=d'} {hμ : μ=ν} :
    ProcedureOrder (ProcedureOrigins.reindex B f hf o (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hμ)) js := by
  subst a' b' l' d' ν; exact ho

variable (B f hf)

private theorem order_shrink (i : Fin S.steps) : ProcedureOrder (shrinkOrigins B f hf i) [i.val] := by
  intro g n h X; subst n
  exact ⟨[],rfl,fun _ ↦ rfl⟩

private theorem order_refresh : ProcedureOrder (refreshOrigins B f hf) [S.steps] := by
  intro g n h X; subst n
  exact ⟨[],rfl,fun _ ↦ rfl⟩

private theorem order_prefix (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureOrder (prefixOrigins B f hf j hj) (List.range j) := by
  induction j with
  | zero => rw [prefixOrigins]; exact order_reindex (order_id _)
  | succ j ih =>
    rw [prefixOrigins,List.range_succ]
    exact order_reindex (order_seq (ih _) (order_reindex (order_shrink B f hf ⟨j,hj⟩)))

private theorem order_block : ProcedureOrder (blockOrigins B f hf) (List.range (S.steps+1)) := by
  rw [List.range_succ]
  exact order_reindex (order_seq (order_reindex (order_prefix B f hf S.steps le_rfl)) (order_refresh B f hf))

private theorem order_repeat (g T n : ℕ) (h : n=T*S.laneBits+g) (X : State (S.degreeExponent 0) n) :
    OrderMatches _ (repeatOrigins B f hf g T n h X) (List.replicate T (List.range (S.steps+1))).flatten := by
  induction T generalizing n with
  | zero => exact order_id _ _ _ _ _
  | succ t ih =>
    let E := (B.procedure f hf).run (t*S.laneBits+g) n (by rw [h,Nat.succ_mul]; omega) X
    exact order_bind E _ _ _ (order_block B f hf _ _ _ X) (fun z ↦ ih _ rfl (E.finalState z))

private theorem collect_ordinals {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E) {js : List ℕ}
    (ho : OrderMatches E o js) (z : E.Choices) :
    (collectLevels B f hf E W r o z).map (fun v ↦ v.origin.ordinal) = js := by
  induction E generalizing js with
  | done => exact ho.symm
  | more p tail ih =>
    obtain ⟨t,rfl,ht⟩ := ho
    exact congrArg (o.1.ordinal :: ·) (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) (ht z.1) z.2)

/-- On every branch, the exact chronological kernel sequence is the fixed
calendar block repeated the prescribed number of times. -/
theorem executeLevels_order {n : ℕ} (T : ℕ) (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    (executeLevels B f hf T h X z).map (fun v ↦ v.origin.ordinal) =
      (List.replicate T (List.range (S.steps+1))).flatten :=
  collect_ordinals B f hf _ _ _ _ (order_repeat B f hf _ T n (Nat.add_sub_of_le h).symm X) z

end CompressorRecords

end

end VPVNP
end Computability
end OAI
