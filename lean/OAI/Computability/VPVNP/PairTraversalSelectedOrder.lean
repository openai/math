import OAI.Computability.VPVNP.PairTraversalRows

/-!
# The order of placement fibers throughout a selected compressor branch

The shrink and refresh readers both enumerate children in the numerical order
of the preceding state. Joining procedures and repeating the compression block
preserve these orders along each branch of the selected kernel history.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel Compression

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}

open Classical in
/-- Every child list uses the restriction of the numbering at its input layer. -/
def OrderedChildren {N Y : Network} (c : TermChain R N Y) (r : ChainParsers κ c)
    (orders : ChainOrders c) (old : Order N.Site) : Prop :=
  match c with
  | .done _ => True
  | .more t _ tail =>
    (∀ v, r.1.order.children v = old.restrict (fun u => v = t.place u)) ∧
      OrderedChildren tail r.2 orders.2 orders.1

open Classical in
/-- The local descriptor uses the actual child, outgoing, and incoming orders of its source state. -/
def PassOrders {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}
    {W : p.MapWitnesses κ} (r : PassReaders p W) : Prop :=
  (∀ i v, (r.order i).children v = (siteOrder X).restrict (fun u => v = (p.step.term i).place u)) ∧
    (∀ i u, (r.order i).outgoing u = outgoingOrder X u) ∧
    ∀ i u, (r.order i).incoming u = incomingOrder X u

/-- Orders at all stages and all choices of this execution. -/
def ExecutionOrders {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → Prop
  | .done _, _, _ => True
  | .more _ tail, W, r => PassOrders r.1 ∧ ∀ i, ExecutionOrders (tail i) (W.2 i) (r.2 i)

open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds

private def castOrders {N M Y : Network} (h : N = M) (c : TermChain R M Y) (r : ChainOrders c) :
    ChainOrders (h.symm ▸ c : TermChain R N Y) := by cases h; exact r

private theorem branch_ordered {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) (rec : E.Records) (z : E.Choices)
    (h : ExecutionOrders E W r) :
    OrderedChildren (E.termChain rec z) (branchParsers E W r rec z)
      (branchOrders E rec z) (siteOrder X) := by
  induction E with
  | done => trivial
  | more p tail ih =>
    refine ⟨h.1.1 z.1, ?_⟩
    have htail := ih z.1 (W.2 z.1) (r.2 z.1) (rec.2 z.1) z.2 (h.2 z.1)
    let c := (tail z.1).termChain (rec.2 z.1) z.2
    let parsers := branchParsers (tail z.1) (W.2 z.1) (r.2 z.1) (rec.2 z.1) z.2
    let orders := branchOrders (tail z.1) (rec.2 z.1) z.2
    have transport {N M Y : Network} (e : N = M) (d : TermChain R M Y)
        (pars : ChainParsers κ d) (ord : ChainOrders d) (s : Order M.Site)
        (hd : OrderedChildren d pars ord s) :
        OrderedChildren (e.symm ▸ d : TermChain R N Y) (castParsers e.symm d pars)
          (castOrders e d ord) (e.symm ▸ s) := by
      cases e
      exact hd
    exact transport (p.output_eq z.1) c parsers orders (siteOrder (p.next z.1)) htail

private theorem executionOrdered_bind {a g b n b' n' : ℕ} {X : State a g}
    (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (W : E.MapWitnesses κ) (V : ∀ z, (f z).MapWitnesses κ)
    (r : ExecutionReaders E W) (s : ∀ z, ExecutionReaders (f z) (V z))
    (h : ExecutionOrders E W r) (hs : ∀ z, ExecutionOrders (f z) (V z) (s z)) :
    ExecutionOrders (E.bind f) _ (bindReaders E f W V r s) := by
  induction E with
  | done => exact hs ()
  | more _ _ ih =>
    exact ⟨h.1, fun i => ih i _ (W.2 i) _ (r.2 i) _ (h.2 i) (fun z => hs ⟨i, z⟩)⟩

variable {a b l d : ℕ} {μ : ℝ}

private abbrev procedureOrdered {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    (r : ProcedureReaders P W) : Prop :=
  ∀ g n h X, ExecutionOrders (P.run g n h X) _ (r g n h X)

private theorem procedureOrdered_id (a : ℕ) (κ : L → R) :
    procedureOrdered (ProcedureReaders.id a κ) := by
  intro g n h X
  have eqn := h.trans (Nat.zero_add g)
  subst g
  trivial

private theorem procedureOrdered_ofPass {A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ) (r : ∀ g X, PassReaders (f g X) (W g X))
    (hr : ∀ g X, PassOrders (r g X)) :
    procedureOrdered (ProcedureReaders.ofPass hd hμ hA f hc he W r) := by
  intro g n h X
  subst n
  exact ⟨hr g X, fun _ => trivial⟩

private theorem procedureOrdered_seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ}
    {Q : Procedure R b c l' d' ν} {W : P.MapWitnesses κ} {V : Q.MapWitnesses κ}
    {r : ProcedureReaders P W} {s : ProcedureReaders Q V}
    (hr : procedureOrdered r) (hs : procedureOrdered s) : procedureOrdered (r.seq s) :=
  fun g n eqn X =>
    let E := P.run (l' + g) n (eqn.trans (Nat.add_assoc l l' g)) X
    executionOrdered_bind E _ _ _ _ _ (hr _ _ _ X) (fun z => hs _ _ _ (E.finalState z))

private theorem procedureOrdered_reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ}
    {W : P.MapWitnesses κ} {r : ProcedureReaders P W} (hr : procedureOrdered r)
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    procedureOrdered (r.reindex (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hμ)) := by
  subst a' b' l' d' μ'
  exact hr

open private prefixReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

variable {k : Type*} [Field k] (S : BlockSchedule k)

private theorem prefix_ordered (shrink : S.ShrinkProcedures R)
    (W : ∀ i, (shrink i).MapWitnesses κ) (r : ∀ i, ProcedureReaders (shrink i) (W i))
    (hr : ∀ i, procedureOrdered (r i)) (j : ℕ) (hj : j ≤ S.steps) :
    procedureOrdered (prefixReaders S shrink W r j hj) := by
  induction j with
  | zero =>
    simp only [prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact procedureOrdered_reindex (procedureOrdered_id _ κ)
  | succ j ih =>
    simp only [prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact procedureOrdered_reindex (procedureOrdered_seq (ih (Nat.le_of_succ_le hj))
      (procedureOrdered_reindex (hr ⟨j, hj⟩)))

private theorem assemble_ordered (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R)
    (W : ∀ i, (shrink i).MapWitnesses κ) (V : refresh.MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (s : ProcedureReaders refresh V)
    (h : ∀ i, procedureOrdered (r i)) (hs : procedureOrdered s) :
    procedureOrdered (assembleReaders S shrink refresh W V r s) := by
  unfold assembleReaders
  exact procedureOrdered_reindex (procedureOrdered_seq
    (procedureOrdered_reindex (prefix_ordered S shrink W r h S.steps le_rfl)) hs)

private theorem repeat_ordered {P : Procedure R a a l d μ} {W : P.MapWitnesses κ}
    {r : ProcedureReaders P W} (hr : procedureOrdered r) (g T n : ℕ)
    (h : n = T * l + g) (X : State a n) :
    ExecutionOrders (P.repeatExecution g T n h X) _ (repeatReaders r g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t * l + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact executionOrdered_bind E _ _ _ _ _ (hr _ _ _ X) (fun z => ih _ rfl (E.finalState z))

variable {S} (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

private theorem shrinkPass_ordered (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    PassOrders (shrinkPassReaders B f hf i h X) := by
  subst n
  exact ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

private theorem block_ordered : procedureOrdered (blockReaders B f hf) := by
  apply assemble_ordered
  · intro i
    apply procedureOrdered_ofPass
    exact fun g X => shrinkPass_ordered B f hf i (packingLaneBits_add _ g) X
  · apply procedureOrdered_ofPass
    intro g X
    exact ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- The actual slot orders on both sides of every visit, through all
repetitions of the shrinking and degree-refresh block. -/
theorem execute_readerOrders {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    ExecutionOrders (B.execute f hf T h X) _
      (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X) :=
  repeat_ordered (block_ordered B f hf) _ T n (Nat.add_sub_of_le h).symm X

/-- In the actual repeated compressor, each local reader visits old positions in the
same order as a scan by their numerical identifiers. -/
theorem selectedParsers_ordered {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T h X).Choices) :
    let E := B.execute f hf T h X
    let recs := B.records f hf T h X
    OrderedChildren (E.termChain recs z) (selectedParsers B f hf T h X z)
      (branchOrders E recs z) (siteOrder X) :=
  branch_ordered _ _ _ _ _
    (execute_readerOrders B f hf T h X)

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
