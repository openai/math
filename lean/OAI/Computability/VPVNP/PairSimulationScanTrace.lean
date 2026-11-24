import OAI.Computability.VPVNP.PairSimulationAssembly
import OAI.Computability.VPVNP.PairSimulationFinalBits

/-!
# Native final-arc calls inside the compressed occurrence count

A trace retains the selector bit strings by level, the chronological native
calls that write the shared final arcs, and one private expansion string
per final site. The final shared assignment is decoded from the very same
native calls used in the trace. Distinct traces remain distinguishable
even when all their parameter exponents agree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel Compression CompressorRecords BurstRAM BurstRAM.PrivateRAM
open scoped Classical

/-- Choice strings observed for a compressed occurrence, grouped into level selectors, shared
final-arc calls and private expansions at the final sites. -/
structure Phases where
  /-- The compact term-selection strings along the chosen history branch, ordered from the
  first pass to the last. -/
  selectors : List (List Bool)
  /-- The branch bits of each native call that writes the terminal shared edge payloads, in
  execution order. -/
  arcCalls : List (List Bool)
  /-- The private expansion strings for the terminal site factors, listed in terminal site
  order. -/
  vertices : List (List Bool)

/-- Extend a continuation trace by putting the current pass's selector string at the front of
its selector list. -/
def Phases.prepend (s : List Bool) (p : Phases) : Phases := ⟨s :: p.selectors, p.arcCalls, p.vertices⟩

private theorem phases_prepend_eq {a b : List Bool} {p q : Phases} (h : Phases.prepend a p = Phases.prepend b q) :
    a = b ∧ p = q := by
  cases p
  cases q
  simpa [Phases.prepend, and_assoc] using h

/-- The path type of the native final-arc phase and its reconstruction
of the unique shared payload assignment. -/
structure ScanPhase (N : Network) where
  /-- The type of successful paths of the shared final-edge scan on this network. -/
  Path : Type
  /-- Bijection decoding a scan path to the shared payload on every edge of the terminal
  network. -/
  payload : Path ≃ ((e : N.Edge) → N.Payload e)
  /-- The chronological list of burst choice strings emitted by a final-edge scan path. This
  list identifies the path uniquely. -/
  calls : Path → List (List Bool)
  calls_injective : Function.Injective calls

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}

/-- A family of final-edge scans indexed by history leaves. At a branch it supplies a scan
family for each possible term choice. -/
def ScanPhases {N : Network} : History A N → Type 1
  | .stop => ScanPhase N
  | .branch s tail => (i : s.Choice) → ScanPhases (tail i)

private abbrev Complete {I : Type} (r : ChoiceReader I) := {bits : List Bool // ∃ i, r.read bits = some (i,[])}

/-- An encoding of occurrences by traces, with a bijection to occurrence indices and observable
phase lists that distinguish the traces. -/
structure TraceEncoding (I : Type) where
  /-- The type of traces that encode the given semantic occurrence indices. -/
  Trace : Type
  /-- Bijection sending each complete trace to the occurrence it represents. -/
  decode : Trace ≃ I
  /-- Extract the observable selector, shared-arc, and private-site strings from an encoded
  trace. -/
  phases : Trace → Phases
  phases_injective : Function.Injective phases

/-- The observable phase lists determine the complete semantic occurrence. -/
noncomputable def TraceEncoding.emitted {I : Type} (t : TraceEncoding I) :
    Set.range t.phases ≃ I := (Equiv.ofInjective t.phases t.phases_injective).symm.trans t.decode

private theorem ordered_bytes_injective {I : Type} (o : Order I) (P : I → List Bool → Prop) :
    Function.Injective (fun xs : (i : I) → {bs // P i bs} => List.ofFn fun i => (xs (o.entries i)).val) := by
  intro xs ys h
  funext i
  obtain ⟨j,rfl⟩ := o.entries.surjective i
  exact Subtype.ext (congrFun (List.ofFn_inj.mp h) j)

/-- Replace just the final shared choice by its native call path. Every
descriptor and site reader still uses the selected term and its exact
map and child arguments. -/
noncomputable def scanTrace {N : Network} (H : History A N) (K : H.KernelWitnesses κ) (r : Readers H K)
    (scan : ScanPhases H) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (read : ∀ v z, ChoiceReader (W v z).Choice) : TraceEncoding (H.expandedWitness K F W).Choice := by
  induction H with
  | @stop N =>
    let rest := fun z : (e : N.Edge) → N.Payload e => (v : N.Site) → Complete
      (read v (WireTensor.edgeAssignment N.src N.dst z v))
    let path := (p : scan.Path) × rest (scan.payload p)
    let bytes (p : path) : Phases := ⟨[], scan.calls p.1, List.ofFn fun j => (p.2 (r.2.1.entries j)).val⟩
    refine ⟨path, ((Equiv.sigmaCongrLeft (β := rest) scan.payload).trans
      (Equiv.sigmaCongrRight (fun z => Equiv.piCongrRight fun v =>
        (read v (WireTensor.edgeAssignment N.src N.dst z v)).completeEquiv.symm))).trans
      (History.stopChoice K F W).symm, bytes, ?_⟩
    rintro ⟨p,u⟩ ⟨q,v⟩ h
    obtain rfl : p = q := scan.calls_injective (congrArg Phases.arcCalls h)
    obtain rfl : u = v := ordered_bytes_injective r.2.1 _ (congrArg Phases.vertices h)
    rfl
  | @branch N s tail ih =>
    let cont (i : s.Choice) := ih i (K.2 i) (r.2.2.2.2 i) (scan i) _ _
      (pushReader (s.term i) (r.2.1 i) r.2.2.1 F W read (K.1 i) (r.2.2.2.1 i))
    let sel := r.1.completeEquiv.symm
    let path := (p : Complete r.1) × (cont (sel p)).Trace
    let bytes (p : path) := Phases.prepend p.1.val ((cont (sel p.1)).phases p.2)
    refine ⟨path, ((Equiv.sigmaCongrLeft (β := fun i => (cont i).Trace) sel).trans
      (Equiv.sigmaCongrRight (fun i => (cont i).decode))).trans (History.branchChoice s tail K F W).symm, bytes, ?_⟩
    rintro ⟨p,u⟩ ⟨q,v⟩ h
    obtain ⟨hs, ht⟩ := phases_prepend_eq h
    obtain rfl : p = q := Subtype.ext hs
    obtain rfl : u = v := (cont (sel p)).phases_injective ht
    rfl

/-- A property of the chronological selectors and native shared arc calls
at all leaves of a history. -/
private def AtTerminals {N : Network} (H : History A N) : (K : H.KernelWitnesses κ) → Readers H K → ScanPhases H →
    (List (List Bool) → List (List Bool) → Prop) → Prop :=
  match H with
  | .stop => fun _ _ scan P => ∀ p : scan.Path, P [] (scan.calls p)
  | .branch _ tail => fun K r scan P => ∀ i, AtTerminals (tail i) (K.2 i) (r.2.2.2.2 i) (scan i)
      (fun sel arcs => P (r.1.encode i :: sel) arcs)

private theorem phases_atTerminals {N : Network} (H : History A N) (K : H.KernelWitnesses κ) (r : Readers H K)
    (scan : ScanPhases H) (F : Factors A N) (W : ∀ v z, MonomialWitness κ (F v z))
    (read : ∀ v z, ChoiceReader (W v z).Choice) (P : List (List Bool) → List (List Bool) → Prop)
    (h : AtTerminals H K r scan P) (x : (scanTrace H K r scan F W read).Trace) :
    let t := (scanTrace H K r scan F W read).phases x
    P t.selectors t.arcCalls := by
  induction H generalizing P with
  | stop => exact h x.1
  | branch s tail ih =>
    let i := r.1.completeEquiv.symm x.1
    have hx := congrArg Subtype.val (r.1.completeEquiv.apply_symm_apply x.1)
    change r.1.encode i = x.1.val at hx
    have ht := ih i (K.2 i) (r.2.2.2.2 i) (scan i) _ _
      (pushReader (s.term i) (r.2.1 i) r.2.2.1 F W read (K.1 i) (r.2.2.2.1 i))
      (fun sels arcs => P (r.1.encode i :: sels) arcs) (h i) x.2
    dsimp only at ht
    rw [hx] at ht
    exact ht

/-- Individual level strings in chronological order along a descriptor path. -/
def selectorCodes {a g b n : ℕ} {X : State a g} :
    (E : StateExecution A b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → E.Choices → List (List Bool)
  | .done _, _, _, _ => []
  | .more _ tail, W, r, z => r.1.select.encode z.1 :: selectorCodes (tail z.1) (W.2 z.1) (r.2 z.1) z.2

section State

variable {a g w p r k : ℕ} (X : State a g)
  (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0)
  (low : ℕ) (pub : M.publicData base = FinalBits.cursor w low 0) (m : Memory w) (extra : ℕ)

private def actualWidth (e : X.network.Edge) : ℕ := X.width ((e.1.1,e.2),e.1.2)

private def scanWidth (i : Fin (edgeOrder X).length) := actualWidth X ((edgeOrder X).entries i)

private theorem scanWidth_sum : ∑ i, scanWidth X i = X.totalWidth := by
  let e : X.network.Edge ≃ (X.Base × Fin (2 ^ a)) × BitWord g := ⟨
    fun x => ((x.1.1,x.2),x.1.2), fun y => ((y.1.1,y.2),y.1.2), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv ((edgeOrder X).entries.trans e) _ _ fun _ => rfl

private def payloadBits (e : X.network.Edge) :
    X.network.Payload e ≃ (Fin (scanWidth X ((edgeOrder X).entries.symm e)) → Bool) := by
  rw [scanWidth, Equiv.apply_symm_apply]
  exact Equiv.refl _

/-- For any linked scan, its successful call sequences are in bijection
with the terminal edge payloads in the physical base, lane and slot order. -/
noncomputable def stateScanPhase (fit : low + X.totalWidth < 2 ^ w) : ScanPhase X.network :=
  let words := FinalBits.payloads (scanWidth X) X.network (edgeOrder X).entries.symm (payloadBits X)
  let read := FinalBits.scanEquiv hl he low _ (by rwa [scanWidth_sum]) pub m extra
  ⟨FinalBits.ScanPaths M.program (extra+9) low (∑ i, scanWidth X i) m, read.symm.trans words,
    Subtype.val, Subtype.val_injective⟩

omit [CommRing A] in
private def castScans {N Y : Network} (e : N = Y) (H : History A N) (s : ScanPhases H) :
    ScanPhases (e ▸ H) := by cases e; exact s

/-- Equip each leaf of a state execution with the linked final-bit scan, using that branch's
final network and its supplied terminal memory. -/
noncomputable def executionScanPhases {b n : ℕ} (E : StateExecution A b n X)
    (memory : E.Choices → Memory w) (fit : ∀ z, low + (E.finalState z).totalWidth < 2 ^ w) : ScanPhases E.history := by
  induction E with
  | done X => exact stateScanPhase X M pc reg base done hl he low pub (memory ()) extra (fit ())
  | more p tail ih =>
    exact fun i => castScans (p.output_eq i).symm _ (ih i (fun z => memory ⟨i,z⟩) (fun z => fit ⟨i,z⟩))

open private transportWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory
open private transportReaders from OAI.Computability.VPVNP.PairSimulationAssembly

private theorem cast_atTerminals {N Y : Network} (e : N = Y) (H : History A N) (W : H.KernelWitnesses κ)
    (r : Readers H W) (scan : ScanPhases H) (P : List (List Bool) → List (List Bool) → Prop)
    (h : AtTerminals H W r scan P) :
    AtTerminals (e ▸ H) (transportWitnesses e H W) (transportReaders e H W r) (castScans e H scan) P := by
  cases e
  exact h

private theorem scan_atTerminals {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2 ^ w)
    (P : List (List Bool) → List (List Bool) → Prop)
    (hp : ∀ z (path : FinalBits.ScanPaths M.program (extra+9) low (E.finalState z).totalWidth (memory z)),
      P (selectorCodes E W r z) path.val) :
    AtTerminals E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P := by
  induction E generalizing P with
  | done X =>
    intro path
    refine hp () ⟨path.val, ?_⟩
    change path.val.length = X.totalWidth ∧
      (runSegment M.program (extra+9) (some (FinalBits.cursor w low X.totalWidth)) (memory ()) path.val).isSome
    simpa only [scanWidth_sum X] using path.prop
  | more p tail ih =>
    exact fun i => cast_atTerminals (p.output_eq i).symm _ _ _ _ _
      (ih i (W.2 i) (r.2 i) (fun z => memory ⟨i,z⟩) (fun z => fit ⟨i,z⟩)
        (fun sels arcs => P (r.1.select.encode i :: sels) arcs) (fun z path => hp ⟨i,z⟩ path))

/-- Every observable trace contains the selectors of one actual branch
and an accepted native shared scan on that same branch's output network
and post-descriptor memory. -/
theorem executionTrace_calls {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2 ^ w) (P : SiteParsers κ X.network) :
    let encoding := scanTrace E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read
    ∀ p : Set.range encoding.phases, ∃ z : E.Choices, p.val.selectors = selectorCodes E W r z ∧
      p.val.arcCalls.length = (E.finalState z).totalWidth ∧
      (runSegment M.program (extra+9) (some (FinalBits.cursor w low (E.finalState z).totalWidth))
        (memory z) p.val.arcCalls).isSome := by
  intro encoding p
  obtain ⟨t, ht⟩ := p.prop
  rw [← ht]
  let ok (sels arcs : List (List Bool)) := ∃ z : E.Choices, sels = selectorCodes E W r z ∧
    arcs.length = (E.finalState z).totalWidth ∧
    (runSegment M.program (extra+9) (some (FinalBits.cursor w low (E.finalState z).totalWidth)) (memory z) arcs).isSome
  exact phases_atTerminals E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
    (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read ok
    (scan_atTerminals X M pc reg base done hl he low pub extra E W r memory fit ok (fun z path => ⟨z,rfl,path.prop⟩)) t

end State

section Cursor

open CursorNetwork CursorRouting

variable {k : Type*} [Field k] {S : BlockSchedule k} {D e w p r k' b l : ℕ} [NeZero D]
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w) (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D)
    (T : ℕ) (hT : T * S.laneBits ≤ l)
variable {ww pp rr kk : ℕ} (N : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
    (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry = pc 0)
    (low : ℕ) (pub : N.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)

private noncomputable abbrev scanInput (S : BlockSchedule k) (e w : ℕ) :=
  cursorState labels hD (Nat.add_sub_of_le S.degree_bounds.1) (ramFieldBits (2^e) w : RAMSystem D → ℕ)

variable (memory : (B.execute f hf T hT (scanInput labels hD S e w)).Choices → Memory ww) (fit : ∀ z : (B.execute f hf T hT (scanInput labels hD S e w)).Choices,
  low + ((B.execute f hf T hT (scanInput labels hD S e w)).finalState z).totalWidth < 2 ^ ww)

/-- A complete compressed occurrence, with its final shared indices
chosen by the linked machine's actual burst calls. -/
noncomputable def compressedScanTrace :
    TraceEncoding (compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT).Choice :=
  let E := B.execute f hf T hT (scanInput labels hD S e w)
  let P := cursorSiteParsers M fuel initial header hw hc labels hD (Nat.add_sub_of_le S.degree_bounds.1) f
  scanTrace E.history (B.executeWitnesses f hf T hT (scanInput labels hD S e w)) (executeReaders B f hf T hT (scanInput labels hD S e w))
    (executionScanPhases (scanInput labels hD S e w) N pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read

/-- The traced occurrences, with their native shared-arc call streams,
retain exactly the original capped machine's weighted count. -/
theorem compressedScanTrace_sum :
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    let paths := compressedScanTrace B f hf M fuel initial header hw hc labels hD T hT N pc reg base done hl he low pub extra memory fit
    letI := Fintype.ofEquiv W.Choice paths.emitted.symm
    ∑ p : Set.range paths.phases, Diagonal.labelMonomial f (W.exponents (paths.emitted p)) =
      (Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^D) header)
        (withinCaps (2^D) (2^e))) : A) := by
  intro W paths
  let :=  Fintype.ofEquiv W.Choice paths.emitted.symm
  exact (Fintype.sum_equiv paths.emitted _ _ fun _ => rfl).trans W.evaluates

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
