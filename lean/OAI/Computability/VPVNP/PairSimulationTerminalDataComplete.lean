import OAI.Computability.VPVNP.PairSimulationTraceJobs

/-! # Reconstructing the trace of every selected branch and terminal witness -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM
open scoped Classical

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}

open private AllData finalParsers_cast from OAI.Computability.VPVNP.PairSimulationTraceJobs
open private castScans from OAI.Computability.VPVNP.PairSimulationScanTrace
open private transportReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private transportWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

private theorem allData_of_traces {N : Network} (H : History A N) (K : H.KernelWitnesses κ) (r : Readers H K)
    (scan : ScanPhases H) (P : SiteParsers κ N) (ok : Phases → Prop)
    (good : let enc := scanTrace H K r scan P.factors P.witnesses P.read
      ∀ q : enc.Trace, ok (enc.phases q)) : AllData H K r scan P (fun phases _ => ok phases) := by
  induction H generalizing ok with
  | stop =>
    intro x
    exact good ⟨x.arcs,fun v => (P.read v _).completeEquiv (x.choices v)⟩
  | branch s tail ih =>
    intro i
    obtain ⟨b,rfl⟩ := r.1.completeEquiv.symm.surjective i
    let i := r.1.completeEquiv.symm b
    let parser : TermParsers κ (s.term i) := ⟨r.2.1 i,r.2.2.1,K.1 i,r.2.2.2.1 i⟩
    let sub := parser.push P
    apply ih i (K.2 i) (r.2.2.2.2 i) (scan i) sub (fun p => ok (Phases.prepend (r.1.encode i) p))
    intro enc q
    have hcode : r.1.encode i = b.val := congrArg Subtype.val (r.1.completeEquiv.apply_symm_apply b)
    rw [hcode]
    exact good ⟨b,q⟩

private theorem allData_uncast {N Y : Network} (e : N=Y) (H : History A N) (K : H.KernelWitnesses κ)
    (r : Readers H K) (scan : ScanPhases H) (P : SiteParsers κ Y) (ok : Phases → (L → ℕ) → Prop)
    (h : AllData (e ▸ H) (transportWitnesses e H K) (transportReaders e H K r) (castScans e H scan) P ok) :
    AllData H K r scan (e.symm ▸ P) ok := by cases e; exact h

variable {a g w p r k : ℕ} (X : State a g)
  (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0) (low : ℕ)
  (pub : M.publicData base = FinalBits.cursor w low 0) (extra : ℕ)

private theorem at_data {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (rec : E.Records) (P : SiteParsers κ X.network) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2^w) (ok : Phases → (L → ℕ) → Prop)
    (h : AllData E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P ok) :
    ∀ z, let scan := stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z)
      ∀ x : TerminalData scan (terminalSites E W r rec P z),
        ok (x.phases (siteOrder (E.finalState z)) (selectorCodes E W r z)) x.exponents := by
  induction E generalizing ok with
  | done X => rintro ⟨⟩; exact h
  | more p tail ih =>
    rintro ⟨i,z⟩
    let nextP := (r.1.termParsers i).push P
    let nextOK := fun phases powers => ok (Phases.prepend (r.1.select.encode i) phases) powers
    have sub := allData_uncast (p.output_eq i).symm (tail i).history ((tail i).historyWitnesses (W.2 i))
      (executionHistoryReaders (tail i) (W.2 i) (r.2 i))
      (executionScanPhases (p.next i) M pc reg base done hl he low pub extra (tail i)
        (fun z => memory ⟨i,z⟩) (fun z => fit ⟨i,z⟩)) nextP nextOK (h i)
    have hsub := ih i (W.2 i) (r.2 i) (rec.2 i) ((p.output_eq i) ▸ nextP) (fun z => memory ⟨i,z⟩)
      (fun z => fit ⟨i,z⟩) nextOK sub z
    have same : terminalSites (.more p tail) W r rec P ⟨i,z⟩ =
        terminalSites (tail i) (W.2 i) (r.2 i) (rec.2 i) ((p.output_eq i) ▸ nextP) z :=
      finalParsers_cast (p.output_eq i).symm _ _ nextP
    rw [same]
    exact hsub

/-- Every chosen descriptor branch, legal shared-arc tape and independent
family of site choices emits a trace, in chronological phase order. -/
theorem terminalData_emits {b n : ℕ} (E : StateExecution A b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (rec : E.Records) (P : SiteParsers κ X.network) (memory : E.Choices → Memory w)
    (fit : ∀ z, low + (E.finalState z).totalWidth < 2^w) :
    let enc := scanTrace E.history (E.historyWitnesses W) (executionHistoryReaders E W r)
      (executionScanPhases X M pc reg base done hl he low pub extra E memory fit) P.factors P.witnesses P.read
    ∀ z, let scan := stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z)
      ∀ x : TerminalData scan (terminalSites E W r rec P z),
        x.phases (siteOrder (E.finalState z)) (selectorCodes E W r z) ∈ Set.range enc.phases := by
  intro enc
  apply at_data X M pc reg base done hl he low pub extra E W r rec P memory fit (fun phases _ => phases ∈ Set.range enc.phases)
  apply allData_of_traces
  exact fun q => ⟨q,rfl⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
