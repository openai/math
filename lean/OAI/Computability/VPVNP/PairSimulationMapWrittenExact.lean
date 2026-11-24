import OAI.Computability.VPVNP.PairSimulationMapWrittenCall
import OAI.Computability.VPVNP.PairSimulationMapCallExact
import OAI.Computability.VPVNP.PairSimulationMapWriterClock

/-!
# Exact chronological trace of a successful descriptor writer and map

The writer's six input words and the external memory determine its ordered
reads. The succeeding native map contributes the exact ticks of the decoded
row sequence. The complete prefix carries the canonical histogram and private
scratch updates on the enclosing machine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapArgumentWriter

open MotifSelector MotifBlocks MotifGrid MotifConversion MotifEntry MotifDemandPadding
open BurstRAM BurstRAM.PrivateRAM InlinePublic MapConstants MapInline
open CompressorRecords CompressorRecords.PhaseRecipe
open scoped Fin.CommRing
open private tick_log from OAI.Computability.VPVNP.PairSimulationMapArgumentWriter

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {r k p R w t : ℕ} (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
  (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)
  (ord : (parameterData B).Entry → Fin t)
  (V : Placement (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r p R)
  (base : Expr) (fields : MapCallSetup.Arg D E → Expr)

local notation "f" => fields ∘ L.args.symm
local notation "loc" => L.corePC L.locations
local notation "d" => demandBits src dst I.party I.demandBits
local notation "x" => mapHalf G (fun _ ↦ inputBits) I.supplyBits

set_option maxHeartbeats 800000 in
-- The writer and inlined map share dependent addresses for all input, staging and output cells.
/-- Native execution of the externally supplied operand recipes and the complete
motif map. The prefix consumes no branch bits. Every external probe belongs to
the fixed argument recipes, and the histogram changes by the emitted ordinals. -/
theorem written_success_exact
    (X : MapEntry.Program.Workspace (callProgram L) I.demand I.payload d x t w)
    (vm : Fin (RegisterSetup.regCount (recipes base f)) ↪ Fin R)
    (inputs : Fin 6 → Fin R) (aux : Fin 3 ↪ Fin R) (place : Address base f → Fin p)
    (M : Machine w p R 11) (link : ∀ a, M.code (place a) =
      (text base f vm inputs aux place (V.entry L.template.entry) a).resize w)
    (safe : ∀ i j, vm i ≠ inputs j) (apart : ∀ i j, vm i ≠ aux j)
    (pointer : V.reg L.ptr = aux 0) (body : MapInline.Linked L ord V M)
    (hw : widthThreshold B ≤ w) (c : Config w p R) (m : Memory w)
    (start : c.pc = setupPC base f place 0) :
    let pub := fun i : Fin 5 ↦ c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := base.eval pub state m
    let outside := fun q : BurstRAM.Word w ↦ q.val < addr.val ∨
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val
    let hist := fun i : Fin t ↦ ((X.hist + i.val : ℕ) : BurstRAM.Word w)
    let names := (runEntry B hp I.demand I.payload I.party d x).1.map (List.map ord)
    addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w →
    (∀ a, (fields a).eval pub state m = MapCallSetup.values L.core loc X a) →
    ResidentFields L.core loc X addr c.privateMem →
    (∀ l, outside (hist l)) →
    (∀ l (i : MapDirectoryInit.Row L.core), hist l ≠ X.directory + (i.val : BurstRAM.Word w)) →
    ∀ (θ : Fin (repetitions B I.demand) → Selector B),
      (selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1 = some θ →
      (∀ e, I.payload e = totalWidth (basePayload B) θ e) →
      let n := factor L ord * entryTicks hp I L ord hw θ
      let es := events base f pub state m ++ List.replicate n (.tick : Event w)
      ∃ (out : Config w p R),
      NodeArguments.ChildScan.Prefix M m c out [] es ∧
      es.length ≤ clock base f + factor L ord * (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand)) ∧
      countProbes es = ∑ i, ((recipes base f) i).loads ∧ choiceBits es = [] ∧
      out.pc = V.entry (callProgram L).done ∧
      out.persistent = c.persistent ∧
      (∀ j, V.privateReg j → (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      (∀ q, outside q → MapCallSetup.Outside L.core loc X q → out.privateMem q = c.privateMem q) ∧
      (∀ l, out.privateMem (hist l) = c.privateMem (hist l) +
        ((names.getD []).count l : BurstRAM.Word w)) ∧
      MapCallSetup.Success L.core loc X (selectorWord B (fits_of_threshold B hw).2.2.2) ord
        (PrivateScratch.write addr (MapCallSetup.values L.core loc X ∘ L.args.symm) c.privateMem)
        out.privateMem ∧
      out.privateMem = (callProgram L).successMemory X
        (selectorWord B (fits_of_threshold B hw).2.2.2) ord θ
          (MapCallSetup.directoryMemory L.core loc X
          (PrivateScratch.write addr (MapCallSetup.values L.core loc X ∘ L.args.symm)
            c.privateMem)) := by
  intro pub state addr outside hist names fit read cells histOutside dirApart θ selected valid n es
  let ev := events base f pub state m
  obtain ⟨mid, len, probes, choices, pc, ptr, per, words, mem, regs, first⟩ :=
    native_exact base f vm inputs aux place (V.entry L.template.entry) M link safe apart
      c m start fit
  have input : MapCallSetup.Input L.core L.args loc X L.ptr (restrict V L.template.entry mid) := by
    apply input_of_published L.core L.args loc X addr c.privateMem _ L.ptr
    · change mid.reg (V.reg L.ptr) = addr
      rw [pointer, ptr]
    · intro a
      change mid.privateMem (addr + ((L.args a).val : BurstRAM.Word w)) = _
      rw [words]
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using read a
    · exact mem
    · exact cells
  obtain ⟨out, bound, tail, keep, savedRegs, savedMem, result, post, done, allMem⟩ :=
    run_entryInput_success_exact ord hp I L V M body hw X mid pc input dirApart θ selected valid
  let ticks := List.replicate n (.tick : Event w)
  change PrimedCounter.GuessWord.Prefix M mid ticks out at tail
  have ht : choiceBits ticks = [] ∧ countProbes ticks = 0 := tick_log n
  have endAt : Outcome X.hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done)
      mid out names := result
  have published : mid.privateMem =
      PrivateScratch.write addr (MapCallSetup.values L.core loc X ∘ L.args.symm) c.privateMem := by
    apply PrivateScratch.eq_write
    · intro i
      exact (words i).trans (read (L.args.symm i))
    · intro q hq
      have cast : (addr.val : BurstRAM.Word w) = addr := Fin.ext (Nat.mod_eq_of_lt addr.isLt)
      exact mem q (PrivateScratch.outside_of_ne addr.val q fun i ↦ cast.symm ▸ hq i)
  have path₁ : NodeArguments.ChildScan.Prefix M m c mid [] ev := first
  have path₂ : NodeArguments.ChildScan.Prefix M m mid out [] ticks := by
    intro fuel more
    simpa only [ht.1] using tail.execute fuel m more
  refine ⟨out, path₁.trans path₂, ?_, ?_, ?_, done, keep.trans per, ?_, ?_, ?_,
    published ▸ post, published ▸ allMem⟩
  · change (ev ++ ticks).length ≤ _
    rw [List.length_append, len, List.length_replicate]
    exact Nat.add_le_add_left bound _
  · change countProbes (ev ++ ticks) = _
    rw [countProbes_append, probes, ht.2, Nat.add_zero]
  · change choiceBits (ev ++ ticks) = _
    rw [PrimedInputRAM.Flow.choiceBits_append, choices, ht.1, List.nil_append]
  · exact fun j hj hv ha ↦ (savedRegs j hj).trans (regs j hv ha)
  · exact fun q ho hmap ↦ (savedMem q hmap).trans (mem q ho)
  · intro l
    cases eq : names with
    | none =>
      rw [eq] at endAt
      simpa [hist] using (endAt.2 l).trans (mem _ (histOutside l))
    | some ls =>
      rw [eq] at endAt
      exact (endAt.2 l).trans
        (congrArg (· + (ls.count l : BurstRAM.Word w)) (mem _ (histOutside l)))

end PairSimulation.MapArgumentWriter

end VPVNP
end Computability
end OAI
