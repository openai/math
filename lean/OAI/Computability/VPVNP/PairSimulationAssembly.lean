import OAI.Computability.VPVNP.PairSimulationHistoryBounds
import OAI.Computability.VPVNP.CompressedRAMMonomials
import OAI.Computability.VPVNP.CompressorShrinkMotifOrder

/-!
# Binary readers for the repeated RAM compressor

The branch selectors read the admitted payload coordinates of each motif.
At the selected term, the layout reader consumes the absorbed fields and
checks the local map entries. These choices compose along the same
branch-dependent executions as the monomial witnesses of equation (12.2).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open CompressorRecords Compression NetworkKernel
open scoped Classical

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}

/-- Enumerate the indices of `Fin n` in increasing order. The position passed to a descriptor
reader is the index itself. -/
def Order.fin (n : ℕ) : Order (Fin n) := ⟨n, Equiv.refl _⟩

/-- Enumerate a pair of ordered sets by dividing a single position among blocks of length
`t.length`. Within the block for an entry of `s`, visit every entry of `t` in order. -/
def Order.prod {I J : Type} (s : Order I) (t : Order J) : Order (I × J) :=
  ⟨s.length * t.length, finProdFinEquiv.symm.trans (s.entries.prodCongr t.entries)⟩

/-- Scanning a descriptor list and retaining just the records in one fiber
preserves the relative order of their numerical identifiers. -/
noncomputable def Order.restrict {I : Type} (s : Order I) (P : I → Prop) [Fintype (Subtype P)] :
    Order (Subtype P) :=
  letI := LinearOrder.lift' (fun x : Subtype P => s.entries.symm x.val)
    (s.entries.symm.injective.comp Subtype.val_injective)
  ⟨Fintype.card _, (Fintype.orderIsoFinOfCardEq _ rfl).toEquiv⟩

/-- Site order follows the stored base numbering and the binary lane
coordinate. Each site's outgoing slots then occur in slot-number order. -/
def siteOrder {a g : ℕ} (X : State a g) : Order X.network.Site :=
  Order.prod ⟨_, X.baseIndex.symm⟩ ⟨_, (bitWordFinEquiv g).symm⟩

/-- Order all outgoing edges first by their source site's base and lane coordinates, then by
their slot number. The terminal history reader uses this order to read one payload per
edge. -/
def edgeOrder {a g : ℕ} (X : State a g) : Order X.network.Edge :=
  (siteOrder X).prod (Order.fin (2 ^ a))

/-- A descriptor supplies the selection parser and the ordered data for
each of the resulting local kernel checks. The old arc payloads are the
bit words in the current lifted state. -/
structure PassReaders {a g b n : ℕ} {X : State a g} (p : StatePass R X b n)
    (W : p.MapWitnesses κ) where
  /-- Binary reader for the choice of term at this pass. The selected index determines which
  local ordering, kernel readers and successor state apply. -/
  select : ChoiceReader p.step.Choice
  /-- For each selected term, specify the order of each site's children and the outgoing and
  incoming incidences read at those children. -/
  order : ∀ i, LocalOrder (p.step.term i)
  /-- Reader for the local monomial witness at output site `v` of term `i`, given the old
  half-edge assignments `x` of its children and the new half-edge assignment `z`. -/
  kernel : ∀ i v x z, ChoiceReader (W i v x z).Choice

/-- All the local parsers, indexed by the original execution and its
monomial witnesses. -/
def ExecutionReaders {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → E.MapWitnesses κ → Type
  | .done _, _ => Unit
  | .more p tail, W => PassReaders p W.1 × ((i : p.step.Choice) → ExecutionReaders (tail i) (W.2 i))

open private transportWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

private def transportReaders {N Y : Network} (e : N = Y) (H : History R N)
    (W : H.KernelWitnesses κ) (r : Readers H W) :
    Readers (e ▸ H) (transportWitnesses e H W) := by
  cases e
  exact r

/-- At a terminal state, read each arc once and pass the assignment to
all sites. At intermediate states, the output identification transports
the continuation and its parsers together. -/
noncomputable def executionHistoryReaders {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) : Readers E.history (E.historyWitnesses W) := by
  induction E with
  | done X => exact ⟨edgeOrder X, siteOrder X, statePayload X⟩
  | @more a g b' n' X p tail ih =>
    exact ⟨r.1.select, r.1.order, statePayload X, r.1.kernel,
      fun i => transportReaders (p.output_eq i).symm _ _ (ih i (W.2 i) (r.2 i))⟩

/-- When two executions are joined, read the continuation selected by the
full choice of the first execution, preserving the same selector stream. -/
noncomputable def bindReaders {b' n' a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (W : E.MapWitnesses κ) (V : ∀ z, (f z).MapWitnesses κ)
    (r : ExecutionReaders E W) (s : ∀ z, ExecutionReaders (f z) (V z)) :
    ExecutionReaders (E.bind f) (E.bindWitnesses f W V) := by
  induction E with
  | done X => exact s ()
  | more p tail ih => exact ⟨r.1, fun i => ih i _ (W.2 i) (fun z => V ⟨i,z⟩) (r.2 i) (fun z => s ⟨i,z⟩)⟩

variable {a b l d : ℕ} {μ : ℝ}

/-- Readers on every input with the correct number of lanes. -/
abbrev ProcedureReaders (P : Procedure R a b l d μ) (W : P.MapWitnesses κ) :=
  ∀ g n h X, ExecutionReaders (P.run g n h X) (W g n h X)

namespace ProcedureReaders

/-- Supply the empty execution reader for the identity procedure. Its input is already the
final state, so there is no pass choice or kernel to parse. -/
def id (a : ℕ) (κ : L → R) : ProcedureReaders (Procedure.id R a) (Procedure.MapWitnesses.id a κ) := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g
  exact ()

/-- Lift readers for each admissible input of a single pass to readers for its one-step
procedure. Each term uses the supplied pass reader and leads directly to the terminal
execution. -/
def ofPass {C : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + C * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ) (r : ∀ g X, PassReaders (f g X) (W g X)) :
    ProcedureReaders (Procedure.ofPass hd hμ hC f hc he) (Procedure.MapWitnesses.ofPass hd hμ hC f hc he W) := by
  intro g n h X
  subst n
  exact ⟨r g X, fun _ => ()⟩

/-- Compose two procedure readers along their executions. Each full choice of the first
procedure supplies the final state on which the second procedure's reader starts. -/
noncomputable def seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {W : P.MapWitnesses κ} {V : Q.MapWitnesses κ} (r : ProcedureReaders P W) (s : ProcedureReaders Q V) :
    ProcedureReaders (P.seq Q) (W.seq V) :=
  fun g n h X =>
    let E := P.run (l'+g) n (h.trans (Nat.add_assoc l l' g)) X
    bindReaders E _ (W _ _ _ X) _ (r _ _ _ X) (fun z => s _ _ _ (E.finalState z))

/-- Transport readers and their map witnesses across equalities of the procedure's input and
output exponents, consumed lanes, position factor and energy coefficient. -/
def reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    (r : ProcedureReaders P W) {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    ProcedureReaders (P.reindex ha hb hl hd hμ) W.reindex := by
  subst a' b' l' d' μ'
  exact r

end ProcedureReaders

/-- Build readers for `T` iterations of a procedure that consumes `l` lane bits each time and
leaves `g` at the end. The continuation uses the state selected by the preceding iteration. -/
noncomputable def repeatReaders {P : Procedure R a a l d μ} {W : P.MapWitnesses κ} (r : ProcedureReaders P W) (g : ℕ) :
    (T n : ℕ) → (h : n = T*l + g) → (X : State a n) →
      ExecutionReaders (P.repeatExecution g T n h X) (Procedure.repeatWitnesses W g T n h X)
  | 0, n, h, X => ProcedureReaders.id a κ g n (by simpa using h) X
  | t+1, n, h, X =>
    let E := P.run (t*l+g) n (by rw [h, Nat.succ_mul]; omega) X
    bindReaders E _ _ _ (r _ _ _ X) (fun z => repeatReaders r g t _ rfl (E.finalState z))


open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

variable {k : Type*} [Field k] (S : BlockSchedule k)

private noncomputable def prefixReaders (shrink : S.ShrinkProcedures R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureReaders (S.shrinkPrefix shrink j hj) (prefixWitnesses S shrink W j hj) :=
  match j with
  | 0 => by
    simp only [prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact (ProcedureReaders.id _ κ).reindex
  | j + 1 => by
    simp only [prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact ((prefixReaders shrink W r j (by omega)).seq (r ⟨j,hj⟩).reindex).reindex

/-- Assemble readers for one scheduled block. Compose the readers of all shrink levels in
schedule order, then attach the refresh reader at the state reached by that sequence. -/
noncomputable def assembleReaders (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R)
    (W : ∀ i : Fin S.steps, (shrink i).MapWitnesses κ) (V : refresh.MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (s : ProcedureReaders refresh V) :
    ProcedureReaders (S.assembleBlock shrink refresh) (S.assembleBlockWitnesses shrink refresh W V) := by
  unfold BlockSchedule.assembleBlock BlockSchedule.assembleBlockWitnesses
  exact ((prefixReaders S shrink W r S.steps le_rfl).reindex.seq s).reindex


section Selectors

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {J D E I : Type} [Fintype J] [Fintype D] [Fintype E] [Fintype I]
  {src dst : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
  (motifs : Order I) (edges : Order E) (hq : ∀ e, 0 < q e) (demand : I → D → ℕ)

/-- One common word width for all nonzero-demand motifs of the pass. -/
noncomputable def selectorWidth : ℕ := (Finset.univ.sup (fun i => outerCap B (demand i))).size

theorem selectorWidth_le (M : ℕ) (hM : ∀ i j, demand i j ≤ M) :
    selectorWidth B demand ≤
      (((∑ j, MotifAdmission.weight p j) + 1) * B.scale * B.radius.num.natAbs *
        MotifAdmission.denominator q).size + Nat.clog 2 (M + 1) := by
  let bound := (((∑ j, MotifAdmission.weight p j) + 1) * B.scale * B.radius.num.natAbs *
    MotifAdmission.denominator q).size + Nat.clog 2 (M+1)
  apply Nat.size_le.mpr
  change Finset.univ.sup (fun i => outerCap B (demand i)) < 2 ^ bound
  apply lt_of_le_of_lt (Finset.sup_le (a := 2 ^ bound - 1) ?_) (by have := Nat.two_pow_pos bound; omega)
  intro i _
  have h : outerCap B (demand i) < 2 ^ bound := Nat.size_le.mp (outerCap_bits_le B (demand i) M (hM i))
  omega

private theorem selector_fits (i : I) : outerCap B (demand i) < 2 ^ selectorWidth B demand :=
  (Finset.le_sup (f := fun j => outerCap B (demand j)) (Finset.mem_univ i)).trans_lt (Nat.lt_size_self _)

/-- Read the admitted coordinates in the fixed motif and supply-edge orders. -/
noncomputable def selectPass : ChoiceReader ((i : I) → ↥(outerIndices B (demand i))) :=
  motifPassReader B motifs.entries edges.entries hq demand (selectorWidth B demand) (selector_fits B demand)

theorem selectPass_bits_le (v : (i : I) → ↥(outerIndices B (demand i))) :
    ((selectPass B motifs edges hq demand).encode v).length ≤ motifs.length * (edges.length * selectorWidth B demand) :=
  motifPass_bits_le B motifs.entries edges.entries hq demand _ (selector_fits B demand) v

end Selectors

section Concrete

variable {S} (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

open MotifGrid MotifConversion ShrinkMotif Refresh

/-- The dense term row is the packed bundle ordinal followed by its CD
rank. This is the same row the native demand and term scans visit. -/
noncomputable def shrinkMotifOrder {a g : ℕ} (X : State a (packingLaneBits a g)) :
    Order X.packingData.Motif :=
  ⟨Fintype.card X.packingData.Motif, CompressorRecords.ShrinkMotifOrder.entries X⟩

set_option maxHeartbeats 2000000 in
/-- Construct the selector and kernel readers of shrink level `i`. They enumerate packed motifs
and the eight supply edges, then read each chosen term's absorbed fields and local map
choices in the restricted site orders. -/
noncomputable def shrinkPassReaders (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    PassReaders (B.shrinkPassAt f hf i h X) (B.shrinkPassWitnesses f hf i h X) := by
  subst n
  let motifs := shrinkMotifOrder X
  let edges := Order.prod ⟨2, finTwoEquiv⟩ (Order.fin 4)
  let parsers := fun s => shrinkStateParsers X B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1
    (S.shrink i) s (fun _ => (motifs.prod (Order.fin 4)).restrict _)
    (fun _ => (motifs.prod (Order.fin 6)).restrict _) (fun _ => (siteOrder X).restrict _)
  exact ⟨selectPass B.shrink motifs edges supplyMass_pos
    (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth),
    fun s => (parsers s).order, fun s => (parsers s).read⟩

set_option maxHeartbeats 2000000 in
/-- Equip the one-pass shrink procedure at level `i` with its concrete binary readers for every
input state satisfying the packing lane count. -/
noncomputable def shrinkProcedureReaders (i : Fin S.steps) :
    ProcedureReaders (B.shrinkProcedure f hf i) (B.shrinkProcedureWitnesses f hf i) :=
  ProcedureReaders.ofPass _ _ _ _ _ _ _
    (fun g X => shrinkPassReaders B f hf i (packingLaneBits_add _ g) X)

/-- Construct the refresh procedure's readers by enumerating base–lane motifs and port–expander
supply edges. After the admitted payload choice, the local parsers use the restricted site
order to read the selected term. -/
noncomputable def refreshProcedureReaders :
    ProcedureReaders (B.refreshProcedure f hf) (B.refreshProcedureWitnesses f hf) := by
  apply ProcedureReaders.ofPass
  intro g X
  let motifs := Order.prod ⟨_, X.baseIndex.symm⟩ ⟨_, (bitWordFinEquiv g).symm⟩
  let edges := (Order.fin (2 ^ S.portExponent)).prod (Order.fin (2 ^ S.expanderExponent))
  have hq (e : Fin (2 ^ S.portExponent) × Fin (2 ^ S.expanderExponent)) : 0 < expanderMass S.baseDegree e := by
    unfold expanderMass BlockSchedule.baseDegree
    positivity
  let parsers := fun c => refreshStateParsers X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
    (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2 c (fun _ => (siteOrder X).restrict _)
  exact ⟨selectPass B.refresh motifs edges hq (blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X)),
    fun c => (parsers c).order, fun c => (parsers c).read⟩

/-- All actual term and entry parsers of the fixed schedule, including
the branch-dependent inputs to its last port refresh. -/
noncomputable def blockReaders : ProcedureReaders (B.procedure f hf) (B.procedureWitnesses f hf) :=
  assembleReaders S _ _ _ _ (shrinkProcedureReaders B f hf) (refreshProcedureReaders B f hf)

/-- Read the history of `T` concrete compressor blocks from `X`. The repeated shrink and
refresh readers follow the selected branches, and the terminal reader visits the final
state's edges and sites. -/
noncomputable def executeReaders {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    Readers (B.execute f hf T h X).history (B.executeWitnesses f hf T h X) :=
  executionHistoryReaders _ _ (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X)

end Concrete

section Cursor

open CursorNetwork CursorRouting BurstRAM BurstRAM.PrivateRAM

variable {S} {D e w p r k' base lanes : ℕ} [NeZero D]
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (M : Machine w p r k') (fuel : ℕ)
  (initial : Word w) (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
  (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D) (T : ℕ) (hT : T * S.laneBits ≤ lanes)

/-- The binary reader for the occurrence type of the repeated compressor
on the padded RAM cursor network, using its actual branch descriptors. -/
noncomputable def compressedReader :
    ChoiceReader (compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT).Choice :=
  let hpad := Nat.add_sub_of_le S.degree_bounds.1
  cursorReader M fuel initial hw hc header labels hD hpad _ _ (executeReaders B f hf T hT _)

/-- The weighted count of complete binary streams is the original capped
path count, with every stream carrying its own parameter exponents. -/
theorem compressed_weightedStreams :
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    let C := compressedReader B f hf M fuel initial header hw hc labels hD T hT
    ∑ bs : successful W C, Diagonal.labelMonomial f (W.exponents (C.completeEquiv.symm bs)) =
      (Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2 ^ D) header)
        (withinCaps (2 ^ D) (2 ^ e))) : R) :=
  weightedStreams _ _

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
