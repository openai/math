import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapWrittenCall

/-!
# Executing the selected grid and party handler

The family supplies the descriptor writer and map subroutine links for the
grid row and party recorded at this visit. The call consumes only deterministic
events, reaches the common advance address or a real rejection, and preserves
all other handler registers and every cell outside its workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerImage.Family

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe MapConstants
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t shared p r w : ℕ}
  (F : Family B t shared) (pc : F.Address → Fin p) (dfs : Fin 9 ↪ Fin r)
  (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r) (own : F.PrivateReg ↪ Fin r)
  (advance : Fin p) (M : Machine w p r 11)
  (installed : ∀ a, M.code (pc a) = (F.text pc dfs saved common own advance a).resize w)
  (banks : F.Apart dfs saved common own)

include installed banks in
theorem native (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B) (hw : widthThreshold B ≤ w)
    (c : Config w p r) (m : Memory w) :
    let i : Index B := (demandGrid B hp I.demand, I.party)
    let L := F.layout i
    let d := demandBits src dst I.party I.demandBits
    let x := mapHalf G (fun _ ↦ inputBits) I.supplyBits
    let inputs := F.inputs dfs saved common i
    let pub := fun j : Fin 5 ↦ c.reg (inputs j.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := (F.base i).eval pub state m
    let outside := fun q : BurstRAM.Word w ↦ q.val < addr.val ∨
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val
    let names := (runEntry B hp I.demand I.payload I.party d x).1.map (List.map F.ordinal)
    ∀ (X : MapEntry.Program.Workspace (MapInline.callProgram L) I.demand I.payload d x t w),
      c.pc = F.target pc i →
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w →
      (∀ a, (F.field i a).eval pub state m =
        MapCallSetup.values L.core (L.corePC L.locations) X a) →
      MapArgumentWriter.ResidentFields L.core (L.corePC L.locations) X addr c.privateMem →
      (∀ l : Fin t, outside ((X.hist + l.val : ℕ) : BurstRAM.Word w)) →
      (∀ (l : Fin t) (j : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (j.val : BurstRAM.Word w)) →
      ∃ out es, NodeArguments.ChildScan.Prefix M m c out [] es ∧
        es.length ≤ MapArgumentWriter.clock (F.base i) (F.fields i) + MapInline.factor L F.ordinal *
          (L.lines.length + (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
            MapNativeClock.cap B i.1 i.2 (repetitions B I.demand)) ∧
        countProbes es = ∑ j, ((MapArgumentWriter.recipes (F.base i) (F.fields i)) j).loads ∧
        choiceBits es = [] ∧ (if names.isSome then out.pc = advance else M.code out.pc = .reject) ∧
        out.persistent = c.persistent ∧
        (∀ q, (∀ a : F.Local i, q ≠ F.localReg own i a) → out.reg q = c.reg q) ∧
        (∀ q, outside q → MapCallSetup.Outside L.core (L.corePC L.locations) X q →
          out.privateMem q = c.privateMem q) ∧
        ∀ l : Fin t, out.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
          c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) +
            ((names.getD []).count l : BurstRAM.Word w) := by
  intro i L d x inputs pub state addr outside names X start fit values resident hist directory
  let V := F.placement pc own advance i
  obtain ⟨writer, body, done, bad⟩ := F.links pc dfs saved common own advance M installed i
  obtain ⟨out, es, pre, len, reads, choice, exit, per, regs, memory, histogram⟩ :=
    MapArgumentWriter.written_call hp I L F.ordinal V (F.base i) (F.field i) X (F.vm own i)
      inputs (F.aux own i) (F.writerPC pc i) M writer (F.vm_safe dfs saved common own banks i)
      (F.vm_aux own i) (F.pointer pc own advance i) body hw c m start fit values resident
      hist directory
  refine ⟨out, es, pre, len, reads, choice, ?_, per, ?_, memory, histogram⟩
  · change out.pc = (if names.isSome then V.entry (MapInline.callProgram L).done
        else V.entry (MapInline.callProgram L).bad) at exit
    cases h : names.isSome
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at exit ⊢
      exact exit ▸ bad
    · simp only [h, ↓reduceIte] at exit ⊢
      exact exit.trans done
  · intro q apart
    apply regs q
    · apply InlinePublic.linked_privateReg
      rintro ⟨v, eq⟩
      exact apart (.inr (.inr v)) eq.symm
    · exact fun v ↦ apart (.inl v)
    · intro v
      fin_cases v <;> exact apart _

/-- All grid and party cases have a common fixed bound for writer probes and a
common linear bound for the full writer and lowered map clock. -/
theorem uniform : ∃ C : ℕ, ∀ (i : Index B) (u : ℕ),
    (∑ j, ((MapArgumentWriter.recipes (F.base i) (F.fields i)) j).loads) ≤ C ∧
    MapArgumentWriter.clock (F.base i) (F.fields i) + MapInline.factor (F.layout i) F.ordinal *
      ((F.layout i).lines.length + (1 + 3 * (MapPortAgreement.ports G i.2
        (F.layout i).core.edgeOrder).length) + MapNativeClock.cap B i.1 i.2 u) ≤ C * (u + 1) := by
  obtain ⟨A, hA⟩ := MapInline.uniform F.ordinal (fun z j ↦ F.layout (z, j))
  let overhead (i : Index B) := MapArgumentWriter.clock (F.base i) (F.fields i) +
    ∑ j, ((MapArgumentWriter.recipes (F.base i) (F.fields i)) j).loads
  let W := ∑ i : Index B, overhead i
  refine ⟨W + A, fun i u ↦ ?_⟩
  have hi : overhead i ≤ W := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (overhead j))
    (Finset.mem_univ i)
  constructor
  · exact ((Nat.le_add_left ..).trans hi).trans (Nat.le_add_right ..)
  · have hclock := ((Nat.le_add_right ..).trans hi).trans
      (Nat.le_mul_of_pos_right W (Nat.succ_pos u))
    simpa only [Nat.add_mul] using Nat.add_le_add hclock (hA i.1 i.2 u)

end PairSimulation.MapHandlerImage.Family

end VPVNP
end Computability
end OAI
