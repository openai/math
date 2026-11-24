import OAI.Computability.VPVNP.CompressorSelectedTerms
import OAI.Computability.VPVNP.CompressorTermWorkerScan
import OAI.Computability.VPVNP.PairSimulationScanTrace

/-!
# Full-word native term tapes and compact semantic selectors

The native ordinal worker guesses each nontrivial coordinate in a machine
word. The local-history reader uses the cap of its current level. Both
choices decode to the same admitted profile at the same physical ordinal.
The resulting equivalence acts only on term selections and preserves each
selected continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM BurstRAM.PrivateRAM
open scoped Classical Fin.CommRing

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates} {A : Type*} [CommRing A]
  {f : B.Entry → A} {hf : B.IsSolution f}
variable {a g b n : ℕ} {X : State a g} {p : StatePass A X b n}

/-- The selected term before reading any bits, in physical motif ordinal order. -/
structure TermRows (G : Grid k) (m M : ℕ) (C : Type) where
  /-- The input demand width for each demand edge of each motif, indexed by physical motif
  ordinal. -/
  demand : Fin m → G.D → ℕ
  bounded : ∀ i e, demand i e ≤ M
  /-- Bijection between a pass term choice and the family of admitted supply profiles for its
  motifs' demand rows. -/
  rows : C ≃ TermRecordScan.Choices G.block demand

set_option maxHeartbeats 1500000 in
/-- Arrange the shrink or refresh motifs in physical ordinal order, with their demand widths
and the corresponding bijection from pass choices to admitted supply profiles. -/
noncomputable def termRows (o : PassOrigin B f hf p) :
    TermRows (grid o) o.motifCount X.maxWireWidth p.step.Choice := by
  cases o with
  | shrink i h X =>
    subst h
    let ids := shrinkMotifOrder X
    let d := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth
    refine ⟨fun j => d (ids.entries j), fun j e => ?_, (Equiv.piCongrLeft (fun u => ↥(MotifConversion.outerIndices B.shrink (d u))) ids.entries).symm⟩
    exact X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) _ e
  | refresh X =>
    let ids := (Order.prod ⟨_, X.baseIndex.symm⟩ ⟨_, (bitWordFinEquiv n).symm⟩)
    let d := Refresh.blockDemandWidths (Refresh.splitSlots X) (bitWordFinEquiv _) (Refresh.splitWidths X)
    refine ⟨fun j => d (ids.entries j), fun j e => ?_, (Equiv.piCongrLeft (fun u => ↥(MotifConversion.outerIndices B.refresh (d u))) ids.entries).symm⟩
    change Refresh.internalWidth _ _ _ _ ≤ _
    unfold Refresh.internalWidth
    split <;> exact X.width_le_maxWireWidth _

/-- The rows used to decode native tapes are the actual demand and supply
coordinates stored by the existing selected term batch. -/
theorem termRows_batch (o : PassOrigin B f hf p) (c : p.step.Choice) :
    (termRows o).demand = (batch o c).demand ∧ ∀ j, ((termRows o).rows c j).val = ((batch o c).choice j).val := by
  cases o with
  | shrink i h X => subst h; exact ⟨rfl,fun _ => rfl⟩
  | refresh X => exact ⟨rfl,fun _ => rfl⟩

/-- The grid-dependent additive word-width constant in the native term scan's bound, before the
logarithmic contribution from the maximum demand width. -/
noncomputable def workerFit (G : Grid k) := (TermWorker.scan_native G.block G.demandOrder.entries
  G.supplyOrder.entries G.pPos G.qPos).choose

/-- Public addressing, input rows, and the integer and instruction bounds
for the fixed ordinal worker on one actual pass. -/
structure WorkerInput (o : PassOrigin B f hf p) (w : ℕ) where
  /-- Addresses and separation bounds for the demand and output term rows of every motif in
  this pass. -/
  layout : TermRecordScan.Layout o.motifCount (grid o).d (grid o).e w
  /-- The worker's four address words in order, giving the demand base, demand stride, term
  base, and term stride. -/
  addr : Fin 4 → Word w
  addresses : TermWorker.Addresses layout addr
  /-- The initial worker memory containing the pass's demand widths at their assigned
  addresses. -/
  memory : Memory w
  inputs : TermRecordScan.Inputs (grid o).demandOrder.entries layout (termRows o).demand memory
  width : workerFit (grid o) + 4 * Nat.clog 2 (X.maxWireWidth+1) ≤ w
  /-- Instruction allowance for each native motif call, large enough for the worker at this
  word width and maximum wire width. -/
  fuel : ℕ
  clock : TermWorker.budget (grid o).block (grid o).d (grid o).e w X.maxWireWidth ≤ fuel

variable {o : PassOrigin B f hf p} {w : ℕ}

/-- Run one term-worker call per motif in ordinal order, starting with cursor zero and the
supplied memory. Successful execution returns the reports for all calls. -/
noncomputable def WorkerInput.run (I : WorkerInput o w) (tapes : Fin o.motifCount → List Bool) :=
  let G := grid o
  runSegment (TermWorker.program G.block G.demandOrder.entries G.supplyOrder.entries I.addr)
    I.fuel (some 0) I.memory (List.ofFn tapes)

/-- Families of per-motif burst tapes for which the native term-worker scan succeeds on this
input. -/
abbrev WorkerInput.Accepted (I : WorkerInput o w) := {tapes : Fin o.motifCount → List Bool // (I.run tapes).isSome}

/-- Encode the selected supply profile at one physical motif ordinal as its native burst tape,
in the grid's supply order and at the worker's coordinate width. -/
noncomputable def workerTapes (o : PassOrigin B f hf p) (w : ℕ) (v : p.step.Choice) (j : Fin o.motifCount) :=
  let G := grid o
  TermRecordScan.tape G.block G.supplyOrder.entries ((termRows o).demand j) w (((termRows o).rows v j).val)

/-- One accepting full-width stream family for every actual term, with
the payload words in their prescribed strided rows. -/
noncomputable def WorkerInput.termEquiv (I : WorkerInput o w) : p.step.Choice ≃ I.Accepted := by
  let G := grid o
  let D := termRows o
  have h := (TermWorker.scan_native G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose_spec
    o.motifCount X.maxWireWidth w I.width I.layout I.addr I.addresses D.demand D.bounded I.memory I.inputs I.fuel I.clock
  have sound := h.1
  have total := h.2
  let encode (v : p.step.Choice) : I.Accepted := ⟨workerTapes o w v, by
    obtain ⟨rs,hr,_⟩ := total (D.rows v)
    exact Option.isSome_iff_exists.mpr ⟨rs,hr⟩⟩
  apply Equiv.ofBijective encode
  constructor
  · intro v u heq
    have eq := congrArg Subtype.val heq
    obtain ⟨v', hv', hu⟩ := (sound _).mp (encode v).prop
    apply D.rows.injective
    exact (hu (D.rows v) rfl).trans (hu (D.rows u) eq).symm
  · intro tapes
    obtain ⟨v,hv,_⟩ := (sound tapes.val).mp tapes.prop
    refine ⟨D.rows.symm v, Subtype.ext ?_⟩
    change (fun j => TermRecordScan.tape G.block G.supplyOrder.entries (D.demand j) w ((D.rows (D.rows.symm v) j).val)) = tapes.val
    rw [Equiv.apply_symm_apply]
    exact hv.symm

theorem WorkerInput.termEquiv_tapes (I : WorkerInput o w) (v : p.step.Choice) :
    (I.termEquiv v).val = workerTapes o w v := rfl

/-- Change the physical bit widths through their common admitted term.
The original decoder of a semantic stream and the native decoder of
its image return the identical branch index. -/
noncomputable def WorkerInput.recode (I : WorkerInput o w) (C : ChoiceReader p.step.Choice) :
    {bs : List Bool // ∃ v, C.read bs = some (v,[])} ≃ I.Accepted :=
  C.completeEquiv.symm.trans I.termEquiv

theorem WorkerInput.recode_term (I : WorkerInput o w) (C : ChoiceReader p.step.Choice)
    (bs : {bs : List Bool // ∃ v, C.read bs = some (v,[])}) :
    I.termEquiv.symm (I.recode C bs) = C.completeEquiv.symm bs := I.termEquiv.symm_apply_apply _

/-- The concrete native pass updates the physical term rows and returns
exactly the re-encoded choice tapes, one burst per motif ordinal. -/
theorem WorkerInput.selected_run (I : WorkerInput o w) (v : p.step.Choice) :
    let G := grid o
    ∃ rs, I.run (I.termEquiv v).val = some rs ∧
      (∀ j, TermRecordScan.Fields G.block G.supplyOrder.entries G.pPos ((batch o v).demand j)
        ((batch o v).choice j).val (I.layout.base j) (after I.memory (eventLog rs))) ∧
      branchPaths rs = List.ofFn (workerTapes o w v) := by
  let G := grid o
  let D := termRows o
  have h := (TermWorker.scan_native G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose_spec
    o.motifCount X.maxWireWidth w I.width I.layout I.addr I.addresses D.demand D.bounded I.memory I.inputs I.fuel I.clock
  obtain ⟨rs,hr,hfield,_,_,_,hbits,_⟩ := h.2 (D.rows v)
  exact ⟨rs,hr,fun j => by simpa only [← (termRows_batch o v).1, ← (termRows_batch o v).2 j] using hfield j,hbits⟩


section Execution

/-- Worker inputs for every pass reachable in an execution, including the input for each
possible continuation after the current term choice. -/
def WorkerInputs {a g b n : ℕ} {X : State a g} :
    (E : StateExecution A b n X) → PassOrigins B f hf E → ℕ → Type
  | .done _, _, _ => Unit
  | .more _ tail, origin, w => WorkerInput origin.1 w × (∀ i, WorkerInputs (tail i) (origin.2 i) w)

/-- One native burst tape per motif, grouped by compression level. -/
noncomputable def ordinalTapes {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X) :
    (origin : PassOrigins B f hf E) → WorkerInputs E origin w → E.Choices → List (List (List Bool)) :=
  match E with
  | .done _ => fun _ _ _ => []
  | .more _ tail => fun origin inputs z =>
    List.ofFn ((inputs.1.termEquiv z.1).val) :: ordinalTapes (tail z.1) (origin.2 z.1) (inputs.2 z.1) z.2

theorem ordinalTapes_injective {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (origin : PassOrigins B f hf E) (inputs : WorkerInputs E origin w) :
    Function.Injective (ordinalTapes E origin inputs) := by
  induction E with
  | done => exact fun (i j : Unit) _ => Subsingleton.elim i j
  | more _ _ ih =>
    rintro ⟨i,u⟩ ⟨j,v⟩ h
    obtain ⟨hs, ht⟩ := List.cons.inj h
    obtain rfl : i = j := inputs.1.termEquiv.injective (Subtype.ext (List.ofFn_inj.mp hs))
    exact congrArg (Sigma.mk i) (ih i (origin.2 i) (inputs.2 i) ht)

theorem selectorCodes_injective {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) : Function.Injective (selectorCodes E W r) := by
  induction E with
  | done => exact fun (i j : Unit) _ => Subsingleton.elim i j
  | more _ _ ih =>
    rintro ⟨i,u⟩ ⟨j,v⟩ h
    obtain ⟨hs,ht⟩ := List.cons.inj h
    obtain rfl : i = j := r.1.select.completeEquiv.injective (Subtype.ext hs)
    exact congrArg (Sigma.mk i) (ih i (W.2 i) (r.2 i) ht)

/-- Observable trace using one native term-worker tape per motif per pass, together with the
final shared-arc calls and private site expansions. -/
structure OrdinalPhases where
  /-- Term-selection burst tapes grouped by compression level and ordered by motif ordinal
  within each level. -/
  termCalls : List (List (List Bool))
  /-- The final shared-edge burst strings belonging to the occurrence selected by the term
  tapes. -/
  arcCalls : List (List Bool)
  /-- The private expansion strings of the terminal sites for this occurrence, in scan order. -/
  vertices : List (List Bool)

/-- The native emission has one term burst per motif and retains the arc
and vertex bursts of the same monomial occurrence. -/
structure SelectorReindex {C : Type} (enc : TraceEncoding C) where
  /-- Assign distinct ordinal-phase traces to the observable phase lists in the original trace
  encoding. -/
  emit : Set.range enc.phases → OrdinalPhases
  injective : Function.Injective emit

/-- Recover the semantic occurrence from an emitted ordinal trace by inverting the emission and
decoding the original phase lists. -/
noncomputable def SelectorReindex.decode {C : Type} {enc : TraceEncoding C} (r : SelectorReindex enc) :
    Set.range r.emit ≃ C := (Equiv.ofInjective r.emit r.injective).symm.trans enc.emitted

theorem SelectorReindex.decode_emit {C : Type} {enc : TraceEncoding C} (r : SelectorReindex enc) (x : Set.range enc.phases) :
    r.decode ⟨r.emit x, x, rfl⟩ = enc.emitted x := by
  simp only [decode, Equiv.trans_apply, Equiv.ofInjective_symm_apply]

private noncomputable def reindexPhases {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (origin : PassOrigins B f hf E)
    (inputs : WorkerInputs E origin w) {C : Type} (enc : TraceEncoding C)
    (branch : Set.range enc.phases → E.Choices)
    (hbranch : ∀ q : Set.range enc.phases, q.val.selectors = selectorCodes E W r (branch q)) : SelectorReindex enc where
  emit q := ⟨ordinalTapes E origin inputs (branch q), q.val.arcCalls, q.val.vertices⟩
  injective := by
    intro x y h
    have hb := ordinalTapes_injective E origin inputs (congrArg OrdinalPhases.termCalls h)
    apply Subtype.ext
    have hs := (hbranch x).trans ((congrArg (selectorCodes E W r) hb).trans (hbranch y).symm)
    have ha := congrArg OrdinalPhases.arcCalls h
    have hv := congrArg OrdinalPhases.vertices h
    cases x with | mk x hx =>
      cases y with | mk y hy =>
        cases x; cases y; exact Phases.mk.injEq .. |>.mpr ⟨hs, ha, hv⟩

variable {a g b n ww pp rr kk : ℕ} (X : State a g)
    (M : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr) (base : Fin kk) (done : Fin pp)
    (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0) (low : ℕ)
    (pub : M.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)

/-- Re-encode every compact level selector by the actual ordinal worker
of that level. The chosen continuation, terminal memory and vertex paths
all refer to the decoded semantic branch. -/
noncomputable def executionReindex (E : StateExecution A b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (origin : PassOrigins B f hf E) (inputs : WorkerInputs E origin w) (P : SiteParsers f X.network)
    (memory : E.Choices → Memory ww) (fit : ∀ z, low + (E.finalState z).totalWidth < 2 ^ ww) :
    let enc := scanTrace E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read
    SelectorReindex enc := by
  intro enc
  let reaches := executionTrace_calls X M pc reg base done hl he low pub extra E W r memory fit P
  exact reindexPhases E W r origin inputs enc (fun q => (reaches q).choose) (fun q => (reaches q).choose_spec.1)

theorem executionReindex_emit (E : StateExecution A b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (origin : PassOrigins B f hf E) (inputs : WorkerInputs E origin w) (P : SiteParsers f X.network)
    (memory : E.Choices → Memory ww) (fit : ∀ z, low + (E.finalState z).totalWidth < 2 ^ ww) :
    let R := executionReindex X M pc reg base done hl he low pub extra E W r origin inputs P memory fit
    ∀ q z, q.val.selectors = selectorCodes E W r z →
      R.emit q = ⟨ordinalTapes E origin inputs z, q.val.arcCalls, q.val.vertices⟩ := by
  intro R q z hz
  let reaches := executionTrace_calls X M pc reg base done hl he low pub extra E W r memory fit P q
  have heq := selectorCodes_injective E W r (reaches.choose_spec.1.symm.trans hz)
  change OrdinalPhases.mk (ordinalTapes E origin inputs reaches.choose) q.val.arcCalls q.val.vertices = _
  rw [heq]

end Execution

section Cursor

open CursorNetwork CursorRouting
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    {D e w p r k' b l : ℕ} [NeZero D] (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ l)
    {ww pp rr kk : ℕ} (N : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
    (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry = pc 0)
    (low : ℕ) (pub : N.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)
    (memory : (B.execute f hf T hT (scanInput labels hD S e w)).Choices → Memory ww)
    (fit : ∀ z : (B.execute f hf T hT (scanInput labels hD S e w)).Choices,
      low + ((B.execute f hf T hT (scanInput labels hD S e w)).finalState z).totalWidth < 2 ^ ww)
    (inputs : WorkerInputs (B.execute f hf T hT (scanInput labels hD S e w))
      (executeOrigins B f hf T hT (scanInput labels hD S e w)) ww)

/-- Re-encode the level selectors of a compressed RAM trace as the actual per-motif worker
tapes along its selected execution branch. -/
noncomputable def compressedReindex :
    SelectorReindex (compressedScanTrace B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit) :=
  let X := scanInput labels hD S e w
  let E := B.execute f hf T hT X
  let P := cursorSiteParsers M fuel initial header hw hc labels hD (Nat.add_sub_of_le S.degree_bounds.1) f
  executionReindex X N pc reg base done hl he low pub extra E _
    (repeatReaders (blockReaders B f hf) _ T l (Nat.add_sub_of_le hT).symm X)
    (executeOrigins B f hf T hT X) inputs P memory fit

/-- The coordinate expansion in the machine-word tapes preserves the full
parameter exponent vector of every path. -/
theorem compressedReindex_exponents :
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    let enc := compressedScanTrace B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit
    let R := compressedReindex B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit inputs
    ∀ q : Set.range enc.phases, W.exponents (R.decode ⟨R.emit q, q, rfl⟩) = W.exponents (enc.emitted q) := by
  intro W enc R q
  exact congrArg W.exponents (R.decode_emit q)

/-- Weighted count with the actual per-motif native selector tapes. -/
theorem compressedReindex_sum :
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    let R := compressedReindex B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit inputs
    letI := Fintype.ofEquiv W.Choice R.decode.symm
    ∑ q : Set.range R.emit, Diagonal.labelMonomial f (W.exponents (R.decode q)) =
      (Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^D) header)
        (withinCaps (2^D) (2^e))) : A) := by
  intro W R
  let := Fintype.ofEquiv W.Choice R.decode.symm
  exact (Fintype.sum_equiv R.decode _ _ fun _ => rfl).trans W.evaluates

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
