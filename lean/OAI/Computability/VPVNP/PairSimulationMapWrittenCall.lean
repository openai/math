import OAI.Computability.VPVNP.PairSimulationMapArgumentInput
import OAI.Computability.VPVNP.PairSimulationMapPost
import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Executing a resident motif call on the enclosing RAM

The descriptor writer reads the external record before control enters the
inlined motif table. Both phases share the caller's private memory. Their
composition gives the event prefix used by the resident-map loop, including
the histogram effect and the frame on the other live operands.
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

/-- Native execution of the externally supplied operand recipes and the complete
motif map. The prefix consumes no branch bits. Every external probe belongs to
the fixed argument recipes, and the histogram changes by the emitted ordinals. -/
theorem written_call_post
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
    ∃ (out : Config w p R) (es : List (Event w)),
      NodeArguments.ChildScan.Prefix M m c out [] es ∧
      es.length ≤ clock base f + factor L ord * (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand)) ∧
      countProbes es = ∑ i, ((recipes base f) i).loads ∧ choiceBits es = [] ∧
      out.pc = (if names.isSome then V.entry (callProgram L).done
        else V.entry (callProgram L).bad) ∧
      out.persistent = c.persistent ∧
      (∀ j, V.privateReg j → (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      (∀ q, outside q → MapCallSetup.Outside L.core loc X q → out.privateMem q = c.privateMem q) ∧
      (∀ l, out.privateMem (hist l) = c.privateMem (hist l) +
        ((names.getD []).count l : BurstRAM.Word w)) ∧
      MapCallSetup.Success L.core loc X (selectorWord B (fits_of_threshold B hw).2.2.2) ord
        (PrivateScratch.write addr (MapCallSetup.values L.core loc X ∘ L.args.symm) c.privateMem)
        out.privateMem := by
  intro pub state addr outside hist names fit read cells histOutside dirApart
  obtain ⟨ev, mid, len, probes, choices, pc, ptr, per, words, mem, regs, first⟩ :=
    native base f vm inputs aux place (V.entry L.template.entry) M link safe apart c m start fit
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
  obtain ⟨n, out, bound, tail, keep, savedRegs, savedMem, result, post⟩ :=
    run_entryInput_post ord hp I L V M body hw X mid pc input dirApart
  let ticks := List.replicate n (.tick : Event w)
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
    simpa only [ticks, (tick_log n).1] using tail.execute fuel m more
  refine ⟨out, ev ++ ticks, path₁.trans path₂, ?_, ?_, ?_, ?_, keep.trans per,
    ?_, ?_, ?_, published ▸ post⟩
  · rw [List.length_append, len, List.length_replicate]
    exact Nat.add_le_add_left bound _
  · rw [countProbes_append, probes, ht.2, Nat.add_zero]
  · rw [PrimedInputRAM.Flow.choiceBits_append, choices, ht.1, List.nil_append]
  · cases eq : names <;> rw [eq] at endAt <;> exact endAt.1
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

/-- The execution prefix, counters, and exterior frame of the same native call. -/
theorem written_call (X : MapEntry.Program.Workspace (callProgram L) I.demand I.payload d x t w)
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
    ∃ (out : Config w p R) (es : List (Event w)),
      NodeArguments.ChildScan.Prefix M m c out [] es ∧
      es.length ≤ clock base f + factor L ord * (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand)) ∧
      countProbes es = ∑ i, ((recipes base f) i).loads ∧ choiceBits es = [] ∧
      out.pc = (if names.isSome then V.entry (callProgram L).done
        else V.entry (callProgram L).bad) ∧
      out.persistent = c.persistent ∧
      (∀ j, V.privateReg j → (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      (∀ q, outside q → MapCallSetup.Outside L.core loc X q → out.privateMem q = c.privateMem q) ∧
      ∀ l, out.privateMem (hist l) = c.privateMem (hist l) +
        ((names.getD []).count l : BurstRAM.Word w) := by
  intro pub state addr outside hist names fit read cells histOutside dirApart
  obtain ⟨out, es, path, cap, probes, choices, pc, per, regFrame, memFrame, counts, _⟩ :=
    written_call_post hp I L ord V base fields X vm inputs aux place M link safe apart pointer
      body hw c m start fit read cells histOutside dirApart
  exact ⟨out, es, path, cap, probes, choices, pc, per, regFrame, memFrame, counts⟩

end PairSimulation.MapArgumentWriter

end VPVNP
end Computability
end OAI
