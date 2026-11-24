import OAI.Computability.VPVNP.PairSimulationNominationAssembly
import OAI.Computability.VPVNP.PairSimulationTraceJobs

/-!
# One selected job family for every native nomination trace

The physical term tapes select the same branch used to interpret the
shared native arc calls. On its output graph the four-half-wire validator
uses the tagged nomination stream. The private vertex strings and the
global exponent vector come from precisely these preorder jobs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM CursorNetwork CursorRouting
open scoped Classical
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) {A : Type*} [CommRing A]
  (f : B.Entry → A) (hf : B.IsSolution f) {d e w n a H s b l : ℕ} [NeZero d]
  {L : PrimedInputRAM.Lengths} {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q s)
  (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (labels : Fin d ≃ Fin b ⊕ Fin l) (hD : 1 < d)
  (t : ℕ) (clock : NominationClock D hw hc t) (T : ℕ) (hT : T * S.laneBits ≤ l)
  {ww pp rr kk : ℕ} (N : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
  (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry = pc 0)
  (low : ℕ) (pub : N.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)
  (memory : (B.execute f hf T hT (scanInput labels hD S e w)).Choices → Memory ww)
  (fit : ∀ z : (B.execute f hf T hT (scanInput labels hD S e w)).Choices,
    low + ((B.execute f hf T hT (scanInput labels hD S e w)).finalState z).totalWidth < 2 ^ ww)
  (inputs : WorkerInputs (B.execute f hf T hT (scanInput labels hD S e w))
    (executeOrigins B f hf T hT (scanInput labels hD S e w)) ww)

theorem nominationOrdinal_jobs :
    let X := scanInput labels hD S e w
    let E := B.execute f hf T hT X
    let origin := executeOrigins B f hf T hT X
    let P := nominationSites D hw hc labels hD (Nat.add_sub_of_le S.degree_bounds.1) f t clock
    let W := compressedRAMCount B f hf D.machine D.fuel 0 D.initial hw hc labels hD T hT
    let R := nominationReindex D hw hc labels hD t clock B f hf T hT N pc reg base done hl he low pub extra memory fit inputs
    ∀ p : Set.range R.emit, ∃ z : E.Choices,
      let Y := E.finalState z
      let scan := stateScanPhase Y N pc reg base done hl he low pub (memory z) extra (fit z)
      let c := E.termChain (B.records f hf T hT X) z
      let r := selectedParsers B f hf T hT X z
      ∃ x : TerminalData scan (finalParsers c r P),
        p.val.termCalls = ordinalTapes E origin inputs z ∧ p.val.arcCalls = scan.calls x.arcs ∧
          ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ),
            let jobs := vertexJobs c r ptr P leaves
            p.val.vertices = List.ofFn (fun j => (x.jobs jobs ((siteOrder Y).entries j)).flatMap VertexJob.bits) ∧
              ∀ label, W.exponents (R.decode p) label = ∑ v, ((x.jobs jobs v).map (fun j => j.increment label)).sum := by
  intro X E origin P W R p
  let readers := repeatReaders (blockReaders B f hf) _ T l (Nat.add_sub_of_le hT).symm X
  obtain ⟨q,hq⟩ := p.prop
  obtain ⟨z,x,hph,hpow⟩ := executionTrace_jobs X N pc reg base done hl he low pub extra E _ readers
    (B.records f hf T hT X) P memory fit q
  have e := executionReindex_emit X N pc reg base done hl he low pub extra E _ readers origin inputs P memory fit q z
    (congrArg Phases.selectors hph)
  change R.emit q = _ at e
  rw [hq] at e
  have dec := R.decode_emit q
  have heq : (⟨R.emit q,q,rfl⟩ : Set.range R.emit) = p := Subtype.ext hq
  rw [heq] at dec
  refine ⟨z,x,congrArg OrdinalPhases.termCalls e,(congrArg OrdinalPhases.arcCalls e).trans (congrArg Phases.arcCalls hph),
    fun ptr leaves => ?_⟩
  let hs := vertexJobs_spec (E.termChain (B.records f hf T hT X) z) (selectedParsers B f hf T hT X z) ptr P leaves
  exact ⟨((congrArg OrdinalPhases.vertices e).trans (congrArg Phases.vertices hph)).trans (x.jobBits _ _ hs _ _),
    fun label => (congrArg (fun c => W.exponents c label) dec).trans ((congrFun hpow label).trans (x.jobPowers _ _ hs label))⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
