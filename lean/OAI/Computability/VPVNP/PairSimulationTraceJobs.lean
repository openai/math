import OAI.Computability.VPVNP.PairSimulationScanTrace
import OAI.Computability.VPVNP.PairSimulationVertexJobs

/-!
# Recovering the selected vertex jobs from an emitted trace

The selector words, the native shared-arc call list, and all vertex strings
in a complete trace come from one branch and one edge assignment. Each
vertex string therefore has the preorder job decomposition for that same
branch, and their exponent increments add to the decoded monomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM
open scoped Classical

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N Y : Network}

/-- The native shared scan supplies the incident values of every vertex
before the independent site witnesses are chosen. -/
structure TerminalData (scan : ScanPhase N) (P : SiteParsers κ N) where
  /-- Path of the shared-arc scan that fixes the wire payload incident at every terminal site. -/
  arcs : scan.Path
  /-- For each terminal site, a local monomial witness choice evaluated on the half-wire
  assignment from the shared-arc path. -/
  choices : ∀ v, (P.witnesses v (WireTensor.edgeAssignment N.src N.dst (scan.payload arcs) v)).Choice

/-- Build the three choice-stream lists from the supplied selector tapes, the shared-arc path's
calls, and each terminal site's encoded witness in site order. -/
def TerminalData.phases {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P)
    (sites : Order N.Site) (sels : List (List Bool)) : Phases :=
  ⟨sels, scan.calls x.arcs, List.ofFn fun j =>
    let v := sites.entries j
    (P.read v (WireTensor.edgeAssignment N.src N.dst (scan.payload x.arcs) v)).encode (x.choices v)⟩

/-- Total exponent of a parameter label in the terminal monomial, obtained by summing its local
witness exponent over all sites of the shared arc assignment. -/
def TerminalData.exponents {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P) (l : L) :=
  ∑ v, (P.witnesses v (WireTensor.edgeAssignment N.src N.dst (scan.payload x.arcs) v)).exponents (x.choices v) l

private def AllData {N : Network} (H : History A N) : (K : H.KernelWitnesses κ) → Readers H K → ScanPhases H →
    SiteParsers κ N → (Phases → (L → ℕ) → Prop) → Prop :=
  match H with
  | .stop => fun _ r scan P ok => ∀ x : TerminalData scan P, ok (x.phases r.2.1 []) x.exponents
  | .branch s tail => fun K r scan P ok => ∀ i,
    let parser : TermParsers κ (s.term i) := ⟨r.2.1 i, r.2.2.1, K.1 i, r.2.2.2.1 i⟩
    AllData (tail i) (K.2 i) (r.2.2.2.2 i) (scan i) (parser.push P)
      (fun phases powers => ok (Phases.prepend (r.1.encode i) phases) powers)

private theorem trace_allData {N : Network} (H : History A N) (K : H.KernelWitnesses κ) (r : Readers H K)
    (scan : ScanPhases H) (P : SiteParsers κ N) (ok : Phases → (L → ℕ) → Prop) (h : AllData H K r scan P ok) :
    let encoded := scanTrace H K r scan P.factors P.witnesses P.read
    ∀ q : encoded.Trace, ok (encoded.phases q) ((H.expandedWitness K P.factors P.witnesses).exponents (encoded.decode q)) := by
  induction H generalizing ok with
  | @stop N =>
    intro enc q
    let x : TerminalData scan P := ⟨q.1, fun v =>
      (P.read v (WireTensor.edgeAssignment N.src N.dst (scan.payload q.1) v)).completeEquiv.symm (q.2 v)⟩
    have same : x.phases r.2.1 [] = enc.phases q := by
      change Phases.mk [] _ _ = Phases.mk [] _ _
      congr 1
      apply congrArg List.ofFn
      funext j
      let v := r.2.1.entries j
      let leaf := P.read v (WireTensor.edgeAssignment N.src N.dst (scan.payload q.1) v)
      exact congrArg Subtype.val (leaf.completeEquiv.apply_symm_apply (q.2 v))
    rw [← same]
    exact h x
  | @branch N s tail ih =>
    intro enc q
    let i := r.1.completeEquiv.symm q.1
    let parser : TermParsers κ (s.term i) := ⟨r.2.1 i, r.2.2.1, K.1 i, r.2.2.2.1 i⟩
    let Q := parser.push P
    let next := fun phases powers => ok (Phases.prepend (r.1.encode i) phases) powers
    have hpart : AllData (tail i) (K.2 i) (r.2.2.2.2 i) (scan i) Q next := h i
    have it := ih i (K.2 i) (r.2.2.2.2 i) (scan i) Q next hpart
    let rest := scanTrace (tail i) (K.2 i) (r.2.2.2.2 i) (scan i) Q.factors Q.witnesses Q.read
    let sub : rest.Trace := q.2
    have hi := it sub
    have hx := congrArg Subtype.val (r.1.completeEquiv.apply_symm_apply q.1)
    change r.1.encode i = q.1.val at hx
    dsimp only [next] at hi
    rw [hx] at hi
    let whole := History.branch s tail
    have decode : enc.decode q = (History.branchChoice s tail K P.factors P.witnesses).symm ⟨i, rest.decode sub⟩ := rfl
    have hp : (whole.expandedWitness K P.factors P.witnesses).exponents (enc.decode q) =
        ((tail i).expandedWitness (K.2 i) Q.factors Q.witnesses).exponents (rest.decode sub) := by
      funext label
      rw [decode]
      exact History.branchChoice_exponents s tail K P.factors P.witnesses i (rest.decode sub) label
    change ok (Phases.prepend q.1.val (rest.phases sub)) ((whole.expandedWitness K P.factors P.witnesses).exponents (enc.decode q))
    rw [hp]
    exact hi

open private castScans from OAI.Computability.VPVNP.PairSimulationScanTrace
open private transportReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private transportWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory
open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds

private theorem allData_cast {N Y : Network} (e : N = Y) (H : History A N) (K : H.KernelWitnesses κ)
    (r : Readers H K) (scan : ScanPhases H) (P : SiteParsers κ Y) (ok : Phases → (L → ℕ) → Prop)
    (h : AllData H K r scan (e.symm ▸ P) ok) :
    AllData (e ▸ H) (transportWitnesses e H K) (transportReaders e H K r) (castScans e H scan) P ok := by
  cases e
  exact h

private theorem finalParsers_cast {N Y Z : Network} (e : N = Y) (c : TermChain A N Z) (r : ChainParsers κ c)
    (P : SiteParsers κ Y) : finalParsers (e ▸ c) (castParsers e c r) P = finalParsers c r (e.symm ▸ P) := by
  cases e
  rfl

/-- Site parsers on the final network of the selected execution branch, formed by pushing the
initial parsers through the chosen terms in order. -/
noncomputable abbrev terminalSites {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) (rec : E.Records) (P : SiteParsers κ X.network) (z : E.Choices) :=
  finalParsers (E.termChain rec z) (branchParsers E W r rec z) P

section Execution

variable {a g w p r k : ℕ} (X : State a g)
  (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0) (low : ℕ)
  (pub : M.publicData base = FinalBits.cursor w low 0) (extra : ℕ)

private theorem execution_allData {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (rec : E.Records) (P : SiteParsers κ X.network) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2^w) (ok : Phases → (L → ℕ) → Prop)
    (h : ∀ z, let scan := stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z)
      ∀ x : TerminalData scan (terminalSites E W r rec P z),
        ok (x.phases (siteOrder (E.finalState z)) (selectorCodes E W r z)) x.exponents) :
    AllData E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P ok := by
  induction E generalizing ok with
  | done X => exact h ()
  | more p tail ih =>
    intro i
    let nextP := (r.1.termParsers i).push P
    let nextOK := fun phases powers => ok (Phases.prepend (r.1.select.encode i) phases) powers
    apply allData_cast (p.output_eq i).symm (tail i).history ((tail i).historyWitnesses (W.2 i))
      (executionHistoryReaders (tail i) (W.2 i) (r.2 i))
      (executionScanPhases (p.next i) M pc reg base done hl he low pub extra (tail i)
        (fun z => memory ⟨i,z⟩) (fun z => fit ⟨i,z⟩)) nextP nextOK
    apply ih i (W.2 i) (r.2 i) (rec.2 i) ((p.output_eq i) ▸ nextP) (fun z => memory ⟨i,z⟩)
      (fun z => fit ⟨i,z⟩) nextOK
    intro z
    have eqSites : terminalSites (.more p tail) W r rec P ⟨i,z⟩ =
        terminalSites (tail i) (W.2 i) (r.2 i) (rec.2 i) ((p.output_eq i) ▸ nextP) z :=
      finalParsers_cast (p.output_eq i).symm _ _ nextP
    have hz := h ⟨i,z⟩
    rw [eqSites] at hz
    exact hz

/-- A single branch, one native shared scan, and actual terminal witnesses
recover all three observable phases and every parameter exponent at once. -/
theorem executionTrace_jobs {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (rec : E.Records) (P : SiteParsers κ X.network) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2^w) :
    let enc := scanTrace E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read
    ∀ q : Set.range enc.phases, ∃ z : E.Choices,
      let scan := stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z)
      ∃ x : TerminalData scan (terminalSites E W r rec P z),
        q.val = x.phases (siteOrder (E.finalState z)) (selectorCodes E W r z) ∧
        (E.history.expandedWitness (E.historyWitnesses W) P.factors P.witnesses).exponents (enc.emitted q) = x.exponents := by
  intro enc q
  let ok (phases : Phases) (powers : L → ℕ) := ∃ z : E.Choices,
    let scan := stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z)
    ∃ x : TerminalData scan (terminalSites E W r rec P z),
      phases = x.phases (siteOrder (E.finalState z)) (selectorCodes E W r z) ∧ powers = x.exponents
  let t := (Equiv.ofInjective enc.phases enc.phases_injective).symm q
  have ht := trace_allData E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
    (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P ok
    (execution_allData X M pc reg base done hl he low pub extra E W r rec P memory fit ok (fun z x => ⟨z,x,rfl,rfl⟩)) t
  change ok q.val _
  change ok (enc.phases t) _ at ht
  rw [show enc.phases t = q.val from Equiv.apply_ofInjective_symm enc.phases_injective q] at ht
  exact ht

end Execution

/-- The individual preorder jobs belonging to the witness at one of the
terminal sites, with both incident halves drawn from the same native scan. -/
def TerminalData.jobs {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P)
    (jobs : JobsFor P) (v : N.Site) : List (VertexJob L) :=
  jobs v (WireTensor.edgeAssignment N.src N.dst (scan.payload x.arcs) v) (x.choices v)

theorem TerminalData.jobBits {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P)
    (trees : N.Site → DFS.VertexTree) (jobs : JobsFor P) (hs : JobsSpec P trees jobs) (o : Order N.Site) (sels) :
    (x.phases o sels).vertices = List.ofFn (fun j => (x.jobs jobs (o.entries j)).flatMap VertexJob.bits) := by
  apply congrArg List.ofFn
  funext j
  exact (hs.bits _ _ _).symm

theorem TerminalData.jobPowers {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P)
    (trees : N.Site → DFS.VertexTree) (jobs : JobsFor P) (hs : JobsSpec P trees jobs) (l : L) :
    x.exponents l = ∑ v, ((x.jobs jobs v).map (fun j => j.increment l)).sum :=
  Finset.sum_congr rfl fun v _ => (hs.increments v _ _ l).symm

section Cursor

open CursorNetwork CursorRouting
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {k : Type*} [Field k] {S : BlockSchedule k} {D e w p r k' b l : ℕ} [NeZero D]
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ l)
    {ww pp rr kk : ℕ} (N : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
    (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry = pc 0)
    (low : ℕ) (pub : N.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)
    (memory : (B.execute f hf T hT (scanInput labels hD S e w)).Choices → Memory ww)
    (fit : ∀ z : (B.execute f hf T hT (scanInput labels hD S e w)).Choices,
      low + ((B.execute f hf T hT (scanInput labels hD S e w)).finalState z).totalWidth < 2 ^ ww)

/-- Every phase triple in the counted RAM family has one selected branch
and shared native arc path whose concrete site jobs produce its vertex
bit strings and whose local increments produce its decoded exponents. -/
theorem compressedTrace_jobs :
    let X := scanInput labels hD S e w
    let E := B.execute f hf T hT X
    let r := repeatReaders (blockReaders B f hf) _ T l (Nat.add_sub_of_le hT).symm X
    let P := cursorSiteParsers M fuel initial header hw hc labels hD (Nat.add_sub_of_le S.degree_bounds.1) f
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    let enc := compressedScanTrace B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit
    ∀ q : Set.range enc.phases, ∃ z : E.Choices,
      let Y := E.finalState z
      let scan := stateScanPhase Y N pc reg base done hl he low pub (memory z) extra (fit z)
      let c := E.termChain (B.records f hf T hT X) z
      let site := selectedParsers B f hf T hT X z
      ∃ x : TerminalData scan (finalParsers c site P),
        q.val.selectors = selectorCodes E _ r z ∧ q.val.arcCalls = scan.calls x.arcs ∧
          ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ),
            let jobs := vertexJobs c site ptr P leaves
            q.val.vertices = List.ofFn (fun j => (x.jobs jobs ((siteOrder Y).entries j)).flatMap VertexJob.bits) ∧
              ∀ label, W.exponents (enc.emitted q) label = ∑ v, ((x.jobs jobs v).map (fun j => j.increment label)).sum := by
  intro X E r P W enc q
  obtain ⟨z,x,hph,hpow⟩ := executionTrace_jobs X N pc reg base done hl he low pub extra E _ r
    (B.records f hf T hT X) P memory fit q
  refine ⟨z,x,congrArg Phases.selectors hph,congrArg Phases.arcCalls hph,fun ptr leaves => ?_⟩
  let c := E.termChain (B.records f hf T hT X) z
  let r' := selectedParsers B f hf T hT X z
  let hs := vertexJobs_spec c r' ptr P leaves
  exact ⟨(congrArg Phases.vertices hph).trans (x.jobBits _ _ hs _ _),
    fun label => (congrFun hpow label).trans (x.jobPowers _ _ hs label)⟩

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
