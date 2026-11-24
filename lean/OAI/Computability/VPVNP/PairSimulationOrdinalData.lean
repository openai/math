import OAI.Computability.VPVNP.PairSimulationTerminalDataComplete
import OAI.Computability.VPVNP.PairSimulationSelectorReindex

/-!
# Physical ordinal emissions and dependent terminal data

An emitted sequence determines its descriptor branch, shared-arc payload
and all independent site witnesses. Conversely every such combination
produces an emission. The inverse recovers the branch used by the actual
ordinal workers, including the physical order of the shared and site tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM
open scoped Classical

private theorem terminal_injective {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N : Network}
    {scan : ScanPhase N} {P : SiteParsers κ N} (o : Order N.Site) (sels : List (List Bool)) :
    Function.Injective (fun x : TerminalData scan P => x.phases o sels) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  obtain rfl : a=b := scan.calls_injective (congrArg Phases.arcCalls h)
  have hv := congrArg Phases.vertices h
  have each := List.ofFn_inj.mp hv
  congr 1
  funext v
  obtain ⟨j,rfl⟩ := o.entries.surjective v
  exact (P.read (o.entries j) _).completeEquiv.injective (Subtype.ext (congrFun each j))

variable {K : Type*} [Field K] {S : BlockSchedule K} {B : S.Templates} {A : Type*} [CommRing A]
  {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w ww p r k : ℕ} (X : State a g)
  (M : Machine ww p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0) (low : ℕ)
  (pub : M.publicData base = FinalBits.cursor ww low 0) (extra : ℕ)
  (E : StateExecution A b n X) (W : E.MapWitnesses f) (rds : ExecutionReaders E W)
  (origin : PassOrigins B f hf E) (inputs : WorkerInputs E origin w) (rec : E.Records) (P : SiteParsers f X.network)
  (memory : E.Choices → Memory ww) (fit : ∀ z, low + (E.finalState z).totalWidth < 2^ww)

/-- One descriptor selection, the corresponding physical final-arc scan,
and one site witness at every vertex of its selected output network. -/
noncomputable abbrev BranchData (z : E.Choices) :=
  TerminalData (stateScanPhase (E.finalState z) M pc reg base done hl he low pub (memory z) extra (fit z))
    (terminalSites E W rds rec P z)

local notation "Data" => BranchData X M pc reg base done hl he low pub extra E W rds rec P memory fit
local notation "R" => executionReindex X M pc reg base done hl he low pub extra E W rds origin inputs P memory fit

/-- Emit the selected branch's physical ordinal-worker tapes together with the final shared-arc
calls and the vertex tapes in site order. -/
noncomputable def ordinalDataPhases (z : E.Choices) (x : Data z) : OrdinalPhases :=
  let phases := x.phases (siteOrder (E.finalState z)) (selectorCodes E W rds z)
  ⟨ordinalTapes E origin inputs z,phases.arcCalls,phases.vertices⟩

local notation "emit" => ordinalDataPhases X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit

private theorem emit_mem (z : E.Choices) (x : Data z) : emit z x ∈ Set.range (R).emit := by
  let phases := x.phases (siteOrder (E.finalState z)) (selectorCodes E W rds z)
  have hp := terminalData_emits X M pc reg base done hl he low pub extra E W rds rec P memory fit z x
  refine ⟨⟨phases,hp⟩,?_⟩
  exact executionReindex_emit X M pc reg base done hl he low pub extra E W rds origin inputs P memory fit _ z rfl

private theorem emit_injective : Function.Injective (fun y : (z : E.Choices) × Data z => emit y.1 y.2) := by
  rintro ⟨z,x⟩ ⟨z',x'⟩ h
  obtain rfl : z=z' := ordinalTapes_injective E origin inputs (congrArg OrdinalPhases.termCalls h)
  apply congrArg (Sigma.mk z)
  apply terminal_injective (siteOrder (E.finalState z)) (selectorCodes E W rds z)
  exact congrArg₂ (Phases.mk (selectorCodes E W rds z)) (congrArg OrdinalPhases.arcCalls h) (congrArg OrdinalPhases.vertices h)

private theorem emit_onto (p : Set.range (R).emit) : ∃ z, ∃ x : Data z, emit z x = p.val := by
  obtain ⟨q,hq⟩ := p.prop
  obtain ⟨z,x,hx,_⟩ := executionTrace_jobs X M pc reg base done hl he low pub extra E W rds rec P memory fit q
  refine ⟨z,x,?_⟩
  have h := executionReindex_emit X M pc reg base done hl he low pub extra E W rds origin inputs P memory fit q z
    (congrArg Phases.selectors hx)
  rw [hq,hx] at h
  exact h.symm

/-- A genuine equivalence in both directions, independent of any physical
acceptance assertion for the online calendar or terminal interpreter. -/
noncomputable def ordinalDataEquiv : ((z : E.Choices) × Data z) ≃ Set.range (R).emit :=
  Equiv.ofBijective (fun y => ⟨emit y.1 y.2,emit_mem X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit y.1 y.2⟩)
    ⟨fun _ _ h => emit_injective X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit (congrArg Subtype.val h),
      fun p => by obtain ⟨z,x,h⟩ := emit_onto X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit p
                  exact ⟨⟨z,x⟩,Subtype.ext h⟩⟩

/-- The three chronological fields of the physical ordinal emission. -/
theorem ordinalDataEquiv_apply (z : E.Choices) (x : Data z) :
    (ordinalDataEquiv X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit ⟨z,x⟩).val =
      emit z x := rfl

set_option maxHeartbeats 1200000 in
/-- The decoded global exponent is exactly the sum of the selected site's
witness exponents in this very terminal occurrence. -/
theorem ordinalDataEquiv_exponents (z : E.Choices) (x : Data z) :
    let p := ordinalDataEquiv X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit ⟨z,x⟩
    (E.history.expandedWitness (E.historyWitnesses W) P.factors P.witnesses).exponents ((R).decode p) = x.exponents := by
  intro p
  obtain ⟨q,hq⟩ := p.prop
  obtain ⟨z',x',hx,hpow⟩ := executionTrace_jobs X M pc reg base done hl he low pub extra E W rds rec P memory fit q
  have h := executionReindex_emit X M pc reg base done hl he low pub extra E W rds origin inputs P memory fit q z'
    (congrArg Phases.selectors hx)
  rw [hq,hx] at h
  have eq : (⟨z,x⟩ : (z : E.Choices) × Data z) = ⟨z',x'⟩ :=
    emit_injective X M pc reg base done hl he low pub extra E W rds origin inputs rec P memory fit h
  have powers := congrArg (fun y : (z : E.Choices) × Data z => y.2.exponents) eq
  have same : (⟨(R).emit q,q,rfl⟩ : Set.range (R).emit) = p := Subtype.ext hq
  rw [← same,SelectorReindex.decode_emit]
  exact hpow.trans powers.symm

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
