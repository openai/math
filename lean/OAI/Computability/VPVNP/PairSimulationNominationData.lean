import OAI.Computability.VPVNP.PairSimulationOrdinalData
import OAI.Computability.VPVNP.PairSimulationNominationJobs

/-! # Complete native ordinal phase data for the virtual nomination counter -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM CursorNetwork CursorRouting
open scoped Classical
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {k : Type*} [Field k] {S : BlockSchedule k} {A : Type*} [CommRing A] {d e w n a H s b l : ℕ} [NeZero d]
  {L : PrimedInputRAM.Lengths} {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q s)
  (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (labels : Fin d ≃ Fin b ⊕ Fin l) (hD : 1 < d)
  (t : ℕ) (clock : NominationClock D hw hc t) (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) (T : ℕ) (hT : T * S.laneBits ≤ l)
  {ww pp rr kk : ℕ} (N : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
  (base : Fin kk) (done : Fin pp) (hl : FinalBits.Linked N pc reg base done) (he : N.entry = pc 0)
  (low : ℕ) (pub : N.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)
  (memory : (B.execute f hf T hT (scanInput labels hD S e w)).Choices → Memory ww)
  (fit : ∀ z : (B.execute f hf T hT (scanInput labels hD S e w)).Choices,
    low + ((B.execute f hf T hT (scanInput labels hD S e w)).finalState z).totalWidth < 2 ^ ww)
  (inputs : WorkerInputs (B.execute f hf T hT (scanInput labels hD S e w))
    (executeOrigins B f hf T hT (scanInput labels hD S e w)) ww)

local notation "X" => scanInput labels hD S e w
local notation "E" => B.execute f hf T hT X
local notation "P" => nominationSites D hw hc labels hD (Nat.add_sub_of_le (And.left S.degree_bounds)) f t clock
local notation "readers" => repeatReaders (blockReaders B f hf) _ T l (Eq.symm (Nat.add_sub_of_le hT)) X
local notation "origin" => executeOrigins B f hf T hT X
local notation "records" => B.records f hf T hT X
local notation "R" => nominationReindex D hw hc labels hD t clock B f hf T hT N pc reg base done hl he low pub extra memory fit inputs

/-- Complete terminal data for each selected chronological descriptor branch
of the actual virtual coefficient counter, including its legal shared scan
and independently selected site histories. -/
noncomputable abbrev NominationData (z : (E).Choices) :=
  BranchData X N pc reg base done hl he low pub extra E _ readers records P memory fit z

/-- Every combination of a legal descriptor selection, a shared payload and
independent valid site histories occurs exactly once in the ordinal image. -/
noncomputable def nominationDataEquiv :
    ((z : (E).Choices) × NominationData D hw hc labels hD t clock B f hf T hT N pc reg base done hl he low pub extra memory fit z) ≃
      Set.range (R).emit :=
  ordinalDataEquiv X N pc reg base done hl he low pub extra E _ readers origin inputs records P memory fit

set_option maxHeartbeats 1200000 in
/-- Exact descriptor and arc calls, per-site preorder tapes, and exponents
of the recovered monomial choice, on the same selected terminal datum. -/
theorem nominationData_jobs :
    ∀ z : (E).Choices, let Y := (E).finalState z
      let scan := stateScanPhase Y N pc reg base done hl he low pub (memory z) extra (fit z)
      let c := (E).termChain records z
      let r := selectedParsers B f hf T hT X z
      ∀ x : TerminalData scan (finalParsers c r P),
        let p := nominationDataEquiv D hw hc labels hD t clock B f hf T hT N pc reg base done hl he low pub extra memory fit inputs ⟨z,x⟩
        let mon := compressedRAMCount B f hf D.machine D.fuel 0 D.initial hw hc labels hD T hT
        p.val.termCalls = ordinalTapes E origin inputs z ∧ p.val.arcCalls = scan.calls x.arcs ∧
          ∀ (ptr : RowPointers c) (leaves : (X).network.Site → ℕ × ℕ),
            let jobs := vertexJobs c r ptr P leaves
            p.val.vertices = List.ofFn (fun j => (x.jobs jobs ((siteOrder Y).entries j)).flatMap VertexJob.bits) ∧
              ∀ label, mon.exponents ((R).decode p) label = ∑ v, ((x.jobs jobs v).map (fun j => j.increment label)).sum := by
  intro z Y scan c r x p mon
  refine ⟨rfl,rfl,fun ptr leaves => ?_⟩
  let hs := vertexJobs_spec c r ptr P leaves
  have hp := ordinalDataEquiv_exponents X N pc reg base done hl he low pub extra E _ readers origin inputs records P memory fit z x
  exact ⟨x.jobBits _ _ hs (siteOrder Y) (selectorCodes E _ readers z),
    fun label => (congrFun hp label).trans (x.jobPowers _ _ hs label)⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
