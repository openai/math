import OAI.Computability.VPVNP.PairSimulationLeafNativeCount
import OAI.Computability.VPVNP.PairSimulationStackSpace
import OAI.Computability.VPVNP.PairSimulationSelectorReindex
import OAI.Computability.VPVNP.PairSimulationVertexJobs

/-!
# Stack nominations as the leaves of the compressed coefficient counter

At a cursor-zero leaf, the binary choices are the stack program's tagged
nomination, followed by its deterministic checks. At a transit leaf the
routing test determines the empty choice. Both readers are transported
into the padded state's original zero-exponent factors before the first
shrinking pass. They therefore compose with the actual term workers and
shared scan on every selected branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression BurstRAM BurstRAM.PrivateRAM
open CursorRouting CursorNetwork Filter
open scoped Classical

variable {d e w n a H s : ℕ} [NeZero d] {L : PrimedInputRAM.Lengths}
  {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q s)
  (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)

/-- A common source clock for all independently chosen incident halves. -/
def NominationClock (t : ℕ) : Prop :=
  ∀ v (z : (validatorNetwork d e w).Half v),
    LeafStartup.steps 52 (LeafStartup.auxiliary D hw hc v (halfBuffers v z)) ≤ t

/-- The same threshold works for all admissible input dimensions and
instances of the auxiliary coefficient machine. -/
theorem eventually_nominationClock :
    ∀ᶠ n : ℕ in atTop, ∀ d e w [NeZero d] (budget : BurstRAM.ProcessorBudget n d e w)
      (L : PrimedInputRAM.Lengths) (a H s : ℕ) (Q : PrimedInputRAM.Layout L n a H w) (D : PrimedCounter.Data Q s),
      D.fuel ≤ n^10 → NominationClock D budget.tags budget.capFits (n^39) := by
  filter_upwards [LeafStartup.eventually_steps 52] with n bound
  intro d e w _ budget L a H s Q D hD v z
  exact bound d e w (LeafStartup.auxiliary D budget.tags budget.capFits v (halfBuffers v z)) budget hD

variable {base lanes degree padding : ℕ} (labels : Fin d ≃ Fin base ⊕ Fin lanes)
    (hd : 1 < d) (hpad : 2+padding = 2^degree)
variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] (f : Label → R)
    (t : ℕ) (clock : NominationClock D hw hc t)

/-- Site parsers for the padded initial cursor network, using the clocked stack-nomination
reader on the incident halves of each underlying leaf. -/
noncomputable def nominationSites :
    SiteParsers f (cursorState labels hd hpad (ramFieldBits (2^e) w : RAMSystem d → ℕ)).network :=
  let bits := (ramFieldBits (2^e) w : RAMSystem d → ℕ)
  let I := cursorStateIso labels hd hpad (ramSystemOrder d) bits
  let P : Factors Type (paddedNetwork d padding bits) := fun v z =>
    initialChoices D.machine D.fuel 0 D.initial hw hc v (unpadHalf padding v z)
  { (cursorSiteParsers D.machine D.fuel 0 D.initial hw hc labels hd hpad f) with
    read := pushLeafReaders I P fun v z => LeafStartup.nominationReader D hw hc v (unpadHalf padding v z) t
      (clock v (unpadHalf padding v z)) }

open private pushLeafReaders_le from OAI.Computability.VPVNP.PairSimulationHistoryBounds

theorem nominationSites_length_le :
    let P := nominationSites D hw hc labels hd hpad f t clock
    ∀ v z p, ((P.read v z).encode p).length ≤ t := by
  let bits := (ramFieldBits (2^e) w : RAMSystem d → ℕ)
  let I := cursorStateIso labels hd hpad (ramSystemOrder d) bits
  let P : Factors Type (paddedNetwork d padding bits) := fun v z =>
    initialChoices D.machine D.fuel 0 D.initial hw hc v (unpadHalf padding v z)
  exact pushLeafReaders_le I P (fun v z => LeafStartup.nominationReader D hw hc v (unpadHalf padding v z) t
    (clock v (unpadHalf padding v z))) t
    (fun v z p => LeafStartup.nominationReader_length_le D hw hc v (unpadHalf padding v z) t (clock _ _) p)

theorem nominationSites_zero :
    let P := nominationSites D hw hc labels hd hpad f t clock
    ∀ v z p label, (P.witnesses v z).exponents p label = 0 := fun _ _ _ _ => rfl

section Compression

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (g : B.Entry → R) (hg : B.IsSolution g)
  (T : ℕ) (hT : T * S.laneBits ≤ lanes)
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

/-- The auxiliary machine count with tagged stack nominations at the
leaves and the same compressed monomial occurrence type. -/
noncomputable def nominationCompressedReader :
    ChoiceReader (compressedRAMCount B g hg D.machine D.fuel 0 D.initial hw hc labels hd T hT).Choice :=
  let X := scanInput labels hd S e w
  let E := B.execute g hg T hT X
  let P := nominationSites D hw hc labels hd (Nat.add_sub_of_le S.degree_bounds.1) g t clock
  historyReader E.history (B.executeWitnesses g hg T hT X) (executeReaders B g hg T hT X) P.factors P.witnesses P.read

theorem nominationCompressed_sum :
    let W := compressedRAMCount B g hg D.machine D.fuel 0 D.initial hw hc labels hd T hT
    let C := nominationCompressedReader D hw hc labels hd t clock B g hg T hT
    ∑ x : successful W C, Diagonal.labelMonomial g (W.exponents (C.completeEquiv.symm x)) =
      (Nat.card (ActualPaths D.machine.program D.fuel 0 (RAMMemory.initialMemory (2^d) D.initial)
        (withinCaps (2^d) (2^e))) : R) :=
  weightedStreams _ _

theorem nominationSelected_length_le :
    let X := scanInput labels hd S e w
    let E := B.execute g hg T hT X
    let P := nominationSites D hw hc labels hd (Nat.add_sub_of_le S.degree_bounds.1) g t clock
    ∀ z : E.Choices, let c := E.termChain (B.records g hg T hT X) z
      let parser := finalParsers c (selectedParsers B g hg T hT X z) P
      ∀ v y x, ((parser.read v y).encode x).length ≤
        B.growthConstant^T * max t (B.growthConstant^T * (X.maxWireWidth+1)) := by
  intro X E P z
  exact selectedSite_length_le B g hg T hT X z P t (nominationSites_length_le D hw hc labels hd
    (Nat.add_sub_of_le S.degree_bounds.1) g t clock)

/-- The reordered leaf choices still decompose into the actual DFS jobs
on the selected history, with all increments supplied by internal maps. -/
theorem nominationSelected_jobs :
    let X := scanInput labels hd S e w
    let E := B.execute g hg T hT X
    let P := nominationSites D hw hc labels hd (Nat.add_sub_of_le S.degree_bounds.1) g t clock
    ∀ z : E.Choices, let c := E.termChain (B.records g hg T hT X) z
      let r := selectedParsers B g hg T hT X z
      ∀ (ptr : RowPointers c) (leaves : X.network.Site → ℕ × ℕ),
        JobsSpec (finalParsers c r P) (chainTrees c r ptr (fun v => leafTree (leaves v)))
          (vertexJobs c r ptr P leaves) := by
  intro X E P z c r ptr leaves
  exact vertexJobs_spec c r ptr P leaves

variable {ww pp rr kk : ℕ} (M : Machine ww pp rr kk) (pc : Fin 10 → Fin pp) (reg : Fin 2 ↪ Fin rr)
  (first : Fin kk) (done : Fin pp) (hl : FinalBits.Linked M pc reg first done) (entry : M.entry = pc 0)
  (low : ℕ) (pub : M.publicData first = FinalBits.cursor ww low 0) (extra : ℕ)
  (memory : (B.execute g hg T hT (scanInput labels hd S e w)).Choices → Memory ww)
  (fit : ∀ z : (B.execute g hg T hT (scanInput labels hd S e w)).Choices,
    low + ((B.execute g hg T hT (scanInput labels hd S e w)).finalState z).totalWidth < 2^ww)

/-- The stack nomination streams and native shared-arc calls for the
same auxiliary coefficient counter. -/
noncomputable def nominationTrace :
    TraceEncoding (compressedRAMCount B g hg D.machine D.fuel 0 D.initial hw hc labels hd T hT).Choice :=
  let X := scanInput labels hd S e w
  let E := B.execute g hg T hT X
  let P := nominationSites D hw hc labels hd (Nat.add_sub_of_le S.degree_bounds.1) g t clock
  scanTrace E.history (B.executeWitnesses g hg T hT X) (executeReaders B g hg T hT X)
    (executionScanPhases X M pc reg first done hl entry low pub extra E memory fit) P.factors P.witnesses P.read

variable (inputs : WorkerInputs (B.execute g hg T hT (scanInput labels hd S e w))
  (executeOrigins B g hg T hT (scanInput labels hd S e w)) ww)

/-- The same stack leaves with full-width ordinal-worker tapes. -/
noncomputable def nominationReindex :
    SelectorReindex (nominationTrace D hw hc labels hd t clock B g hg T hT M pc reg first done hl entry low pub extra memory fit) :=
  let X := scanInput labels hd S e w
  let E := B.execute g hg T hT X
  let P := nominationSites D hw hc labels hd (Nat.add_sub_of_le S.degree_bounds.1) g t clock
  executionReindex X M pc reg first done hl entry low pub extra E _
    (repeatReaders (blockReaders B g hg) _ T lanes (Nat.add_sub_of_le hT).symm X)
    (executeOrigins B g hg T hT X) inputs P memory fit

theorem nominationReindex_sum :
    let W := compressedRAMCount B g hg D.machine D.fuel 0 D.initial hw hc labels hd T hT
    let C := nominationReindex D hw hc labels hd t clock B g hg T hT M pc reg first done hl entry low pub extra memory fit inputs
    letI := Fintype.ofEquiv W.Choice C.decode.symm
    ∑ x : Set.range C.emit, Diagonal.labelMonomial g (W.exponents (C.decode x)) =
      (Nat.card (ActualPaths D.machine.program D.fuel 0 (RAMMemory.initialMemory (2^d) D.initial)
        (withinCaps (2^d) (2^e))) : R) := by
  intro W C
  let := Fintype.ofEquiv W.Choice C.decode.symm
  exact (Fintype.sum_equiv C.decode _ _ fun _ => rfl).trans W.evaluates

end Compression
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
