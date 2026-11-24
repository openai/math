import OAI.Computability.VPVNP.PairSimulationAssembly

/-!
# Per-vertex bit bounds on the actual repeated compressor

The field records of Theorem 7.1 cover each choice read below a selected
vertex. Joining two procedures and repeating a block preserve this
coverage at every selected term. This bounds the private binary string
at each final site, including independent old half-arc guesses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression NetworkKernel CompressorRecords
open scoped Classical

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}

/-- Use the same order, arc payloads and kernel choices as the complete
history reader. -/
noncomputable def PassReaders.termParsers {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}
    {W : p.MapWitnesses κ} (r : PassReaders p W) (i : p.step.Choice) : TermParsers κ (p.step.term i) :=
  ⟨r.order i, statePayload X, W i, r.kernel i⟩

/-- Every term of every reachable pass has enough recorded field width at each output site to
cover the bits for its children's old halves and its local kernel choice. -/
def ExecutionCovered {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → E.Records → Prop
  | .done _, _, _, _ => True
  | .more _ tail, W, r, rec =>
    (∀ i, (r.1.termParsers i).Covered (rec.1 i)) ∧
      ∀ i, ExecutionCovered (tail i) (W.2 i) (r.2 i) (rec.2 i)

private def castParsers {N Y Z : Network} (e : N = Y) (c : TermChain R N Z) (r : ChainParsers κ c) :
    ChainParsers κ (e ▸ c) := by cases e; exact r

private theorem castCovered {N Y Z : Network} (e : N = Y) (c : TermChain R N Z) (r : ChainParsers κ c)
    (h : Covered c r) : Covered (e ▸ c) (castParsers e c r) := by cases e; exact h

/-- Follow the actual term choices into the local subtree parsers of this
branch of the existing compression history. -/
noncomputable def branchParsers {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) (rec : E.Records) (z : E.Choices) :
    ChainParsers κ (E.termChain rec z) := by
  induction E with
  | done => exact PUnit.unit
  | more p tail ih =>
    exact ⟨r.1.termParsers z.1, castParsers (p.output_eq z.1).symm _ (ih z.1 (W.2 z.1) (r.2 z.1) (rec.2 z.1) z.2)⟩

theorem branchParsers_covered {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) (rec : E.Records) (h : ExecutionCovered E W r rec) (z : E.Choices) :
    Covered (E.termChain rec z) (branchParsers E W r rec z) := by
  induction E with
  | done => trivial
  | more p tail ih =>
    exact ⟨h.1 z.1, castCovered (p.output_eq z.1).symm _ _ (ih z.1 _ _ _ (h.2 z.1) z.2)⟩

theorem bindCovered {b' n' a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (W : E.MapWitnesses κ) (V : ∀ z, (f z).MapWitnesses κ)
    (r : ExecutionReaders E W) (s : ∀ z, ExecutionReaders (f z) (V z))
    (u : E.Records) (v : ∀ z, (f z).Records) (hu : ExecutionCovered E W r u)
    (hv : ∀ z, ExecutionCovered (f z) (V z) (s z) (v z)) :
    ExecutionCovered (E.bind f) _ (bindReaders E f W V r s) (E.bindRecords f u v) := by
  induction E with
  | done X => exact hv ()
  | more p tail ih => exact ⟨hu.1, fun i => ih i _ (W.2 i) _ (r.2 i) _ (u.2 i) _ (hu.2 i) (fun z => hv ⟨i,z⟩)⟩

variable {a b l d C m : ℕ} {μ : ℝ}

/-- Coverage of a procedure on every legal input state and lane count. Each branch of the
resulting execution is checked against the records supplied by the procedure's record
bounds. -/
abbrev ProcedureCovered {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    (r : ProcedureReaders P W) (B : P.RecordBounds C m) :=
  ∀ g n h X, ExecutionCovered (P.run g n h X) _ (r g n h X) (B.records g n h X)

namespace ProcedureCovered

theorem id (a C : ℕ) (κ : L → R) :
    ProcedureCovered (ProcedureReaders.id a κ) (Procedure.RecordBounds.id R a C) := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g
  trivial

theorem ofPass {A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ) (r : ∀ g X, PassReaders (f g X) (W g X))
    (rec : ∀ g X, (f g X).Records) (hb : ∀ g X, (f g X).Bounded (rec g X) C)
    (hcov : ∀ g X i, ((r g X).termParsers i).Covered (rec g X i)) :
    ProcedureCovered (ProcedureReaders.ofPass hd hμ hA f hc he W r)
      (Procedure.RecordBounds.ofPass hd hμ hA f hc he rec hb) := by
  intro g n h X
  subst n
  exact ⟨hcov g X, fun _ => trivial⟩

theorem seq {c l' d' D n : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {W : P.MapWitnesses κ} {V : Q.MapWitnesses κ} {r : ProcedureReaders P W} {s : ProcedureReaders Q V}
    {B : P.RecordBounds C m} {B' : Q.RecordBounds D n} (h : ProcedureCovered r B) (h' : ProcedureCovered s B') :
    ProcedureCovered (r.seq s) (B.seq B') :=
  fun g n eqn X =>
    let E := P.run (l'+g) n (eqn.trans (Nat.add_assoc l l' g)) X
    bindCovered E _ _ _ _ _ _ _ (h _ _ _ X) (fun z => h' _ _ _ (E.finalState z))

theorem mono {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    {r : ProcedureReaders P W} {B : P.RecordBounds C m} {D n : ℕ} (h : ProcedureCovered r B)
    (hC : C ≤ D) (hm : m ≤ n) : ProcedureCovered r (B.mono hC hm) := h

theorem reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    {r : ProcedureReaders P W} {B : P.RecordBounds C m} (h : ProcedureCovered r B)
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    ProcedureCovered (r.reindex (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hμ)) B.reindex := by
  subst a' b' l' d' μ'
  exact h

end ProcedureCovered

theorem repeatCovered {P : Procedure R a a l d μ} {W : P.MapWitnesses κ} {r : ProcedureReaders P W}
    {B : P.RecordBounds C m} (hc : ProcedureCovered r B) (g T n : ℕ) (h : n = T*l + g) (X : State a n) :
    ExecutionCovered (P.repeatExecution g T n h X) _ (repeatReaders r g T n h X) (Procedure.repeatRecords B g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t*l+g) n (by rw [h,Nat.succ_mul]; omega) X
    exact bindCovered E _ _ _ _ _ _ _ (hc _ _ _ X) (fun z => ih _ rfl (E.finalState z))

open private prefixReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory
open private prefixRecordBounds from OAI.Computability.VPVNP.CompressionBlockHistory

variable {k : Type*} [Field k] (S : BlockSchedule k)

private theorem prefixCovered (shrink : S.ShrinkProcedures R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ) (r : ∀ i, ProcedureReaders (shrink i) (W i))
    (B : ∀ i, (shrink i).RecordBounds C 1) (h : ∀ i, ProcedureCovered (r i) (B i)) (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureCovered (prefixReaders S shrink W r j hj) (prefixRecordBounds S shrink B j hj) := by
  induction j with
  | zero =>
    simp only [prefixRecordBounds, prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact (ProcedureCovered.id _ C κ).reindex
  | succ j ih =>
    simp only [prefixRecordBounds, prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact (((ih (Nat.le_of_succ_le hj)).seq (h ⟨j,hj⟩).reindex).mono (max_le le_rfl le_rfl) le_rfl).reindex

private theorem assembleCovered (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R)
    {D : Fin S.steps → ℕ} (W : ∀ i, (shrink i).MapWitnesses κ) (V : refresh.MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (s : ProcedureReaders refresh V)
    (B : ∀ i, (shrink i).RecordBounds (D i) 1) (B' : refresh.RecordBounds C 1)
    (h : ∀ i, ProcedureCovered (r i) (B i)) (h' : ProcedureCovered s B') :
    ProcedureCovered (assembleReaders S shrink refresh W V r s) (S.assembleBlockRecords shrink refresh B B') := by
  unfold assembleReaders BlockSchedule.assembleBlockRecords
  apply ProcedureCovered.reindex
  apply ProcedureCovered.seq _ h'
  apply ProcedureCovered.reindex
  exact prefixCovered S shrink W r _ (fun i => h i) S.steps le_rfl


omit [CommRing R] in
private theorem recordWidths_mono {N Y : Network} (c : TermChain R N Y) {u v : ℕ}
    (h : c.AllRecordsLe u) (hle : u ≤ v) : c.AllRecordsLe v := by
  induction c with
  | done => trivial
  | more _ _ _ ih => exact ⟨fun x i => (h.1 x i).trans hle, fun x j => (h.2.1 x j).trans hle, ih h.2.2⟩

section Concrete

open MotifConversion Refresh
open private recordsAt from OAI.Computability.VPVNP.ShrinkProcedureHistory

variable {S} (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

set_option maxHeartbeats 2000000 in
private theorem shrinkPassCovered (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g) (X : State (S.degreeExponent i.castSucc) n)
    (s : (B.shrinkPassAt f hf i h X).step.Choice) :
    ((shrinkPassReaders B f hf i h X).termParsers s).Covered (recordsAt B f hf i h X s) := by
  subst n
  let motifs := shrinkMotifOrder X
  intro v old new ch
  exact shrinkStateParsers_covered X B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i) s
    (fun _ => (motifs.prod (Order.fin 4)).restrict _) (fun _ => (motifs.prod (Order.fin 6)).restrict _)
    (fun _ => (siteOrder X).restrict _) v old new ch

set_option maxHeartbeats 2000000 in
private theorem shrinkProcedureCovered (i : Fin S.steps) :
    ProcedureCovered (shrinkProcedureReaders B f hf i) (B.shrinkProcedureRecords f hf i) :=
  ProcedureCovered.ofPass _ _ _ _ _ _ _ _ _ _ (fun g X => shrinkPassCovered B f hf i (packingLaneBits_add _ g) X)

private theorem refreshProcedureCovered :
    ProcedureCovered (refreshProcedureReaders B f hf) (B.refreshProcedureRecords f hf) := by
  intro g n h X
  subst n
  refine ⟨fun c v old new ch => ?_, fun _ => trivial⟩
  exact refreshStateParsers_covered X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
    (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2 c (fun _ => (siteOrder X).restrict _) v old new ch

theorem blockReaders_covered : ProcedureCovered (blockReaders B f hf) (B.recordBounds f hf) :=
  assembleCovered S _ _ _ _ _ _ _ _ (shrinkProcedureCovered B f hf) (refreshProcedureCovered B f hf)

/-- On a complete choice of terms, use the concrete readers and records
of the compressor to expand one final vertex. -/
noncomputable def selectedParsers {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    ChainParsers f ((B.execute f hf T h X).termChain (B.records f hf T h X) z) :=
  branchParsers _ _ (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X) _ z

theorem selectedParsers_covered {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    Covered ((B.execute f hf T h X).termChain (B.records f hf T h X) z) (selectedParsers B f hf T h X z) :=
  branchParsers_covered _ _ _ _ (repeatCovered (blockReaders_covered B f hf) _ T n (Nat.add_sub_of_le h).symm X) z

/-- The per-site private string uses at most the per-block growth factor
times the larger of the leaf-string bound and the intermediate field bound. -/
theorem selectedSite_length_le {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) (P : SiteParsers f X.network)
    (L : ℕ) (hL : ∀ u a p, ((P.read u a).encode p).length ≤ L) :
    let chain := (B.execute f hf T h X).termChain (B.records f hf T h X) z
    let parsers := finalParsers chain (selectedParsers B f hf T h X z) P
    ∀ v a p, ((parsers.read v a).encode p).length ≤
      B.growthConstant ^ T * max L (B.growthConstant ^ T * (X.maxWireWidth + 1)) := by
  let chain := (B.execute f hf T h X).termChain (B.records f hf T h X) z
  let width := B.growthConstant ^ T * (X.maxWireWidth + 1)
  obtain ⟨_, _, _, counts, records, _⟩ := B.branch_bounds f hf T h X z
  have hrec : chain.AllRecordsLe (max L width) := by
    exact recordWidths_mono chain records (le_max_right _ _)
  have hb := finalParsers_bound chain (selectedParsers B f hf T h X z)
    (selectedParsers_covered B f hf T h X z) P (fun _ => 1) (max L width) hrec
    (fun u a p => (hL u a p).trans (by simp))
  exact fun v a p => (hb v a p).trans (Nat.mul_le_mul_right _ (counts v))

end Concrete

section Cursor

open CursorNetwork CursorRouting BurstRAM BurstRAM.PrivateRAM

variable {S} {D e w p r k' base lanes : ℕ} [NeZero D]
    (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2^D * 2^e < 2^w) (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ lanes)

/-- The bound on private bits at every final vertex, specialized to the
original capped machine's validating leaf bursts. -/
theorem cursorSite_length_le :
    let hpad := Nat.add_sub_of_le S.degree_bounds.1
    let X := cursorState labels hD hpad (ramFieldBits (2^e) w : RAMSystem D → ℕ)
    let E := B.execute f hf T hT X
    let P := cursorSiteParsers M fuel initial header hw hc labels hD hpad f
    ∀ z : E.Choices, let chain := E.termChain (B.records f hf T hT X) z
      let parsers := finalParsers chain (selectedParsers B f hf T hT X z) P
      ∀ v a p, ((parsers.read v a).encode p).length ≤
        B.growthConstant^T * max (2 * 2^e * (fuel+w)) (B.growthConstant^T * (X.maxWireWidth+1)) := by
  intro hpad X E P z
  exact selectedSite_length_le B f hf T hT X z P _ (cursorSiteParsers_length_le M fuel initial header hw hc labels hD hpad f)

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
