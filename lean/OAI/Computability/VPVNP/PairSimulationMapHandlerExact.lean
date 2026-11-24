import OAI.Computability.VPVNP.PairSimulationMapHandlerAction
import OAI.Computability.VPVNP.PairSimulationMapHandlerRun
import OAI.Computability.VPVNP.PairSimulationMapWrittenExact

/-!
# Native executions of the deterministic grid and party actions

A successful action fixes the chronological event list and the complete upper
scratch of the same execution prefix. An unsuccessful action executes into a
rejecting instruction of its selected handler.
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
theorem native_success_exact (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (hw : widthThreshold B ≤ w) (c : Config w p r) (m : Memory w) :
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
    ∀ (X : MapEntry.Program.Workspace (MapInline.callProgram L) I.demand I.payload d x t w)
      (endAddr : ℕ) (savedScratch : DFS.Scratch w endAddr),
      DFS.scratch endAddr c.privateMem = savedScratch → names.isSome = true →
      c.pc = F.target pc i →
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w →
      (∀ a, (F.field i a).eval pub state m =
        MapCallSetup.values L.core (L.corePC L.locations) X a) →
      MapArgumentWriter.ResidentFields L.core (L.corePC L.locations) X addr c.privateMem →
      (∀ l : Fin t, outside ((X.hist + l.val : ℕ) : BurstRAM.Word w)) →
      (∀ (l : Fin t) (j : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (j.val : BurstRAM.Word w)) →
      let es := F.successEvents hp I hw pub state m
      ∃ out, NodeArguments.ChildScan.Prefix M m c out [] es ∧
        es.length ≤ MapArgumentWriter.clock (F.base i) (F.fields i) + MapInline.factor L F.ordinal *
          (L.lines.length + (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
            MapNativeClock.cap B i.1 i.2 (repetitions B I.demand)) ∧
        countProbes es = ∑ j, ((MapArgumentWriter.recipes (F.base i) (F.fields i)) j).loads ∧
        choiceBits es = [] ∧ out.pc = advance ∧
        out.persistent = c.persistent ∧
        (∀ q, (∀ a : F.Local i, q ≠ F.localReg own i a) → out.reg q = c.reg q) ∧
        (∀ q, outside q → MapCallSetup.Outside L.core (L.corePC L.locations) X q →
          out.privateMem q = c.privateMem q) ∧
        (∀ l : Fin t, out.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
          c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) +
            ((names.getD []).count l : BurstRAM.Word w)) ∧
        DFS.scratch endAddr out.privateMem = MapScratch.upper L.core L.args (L.corePC L.locations)
          X addr (selectorWord B (fits_of_threshold B hw).2.2.2) F.ordinal endAddr
            savedScratch := by
  intro i L d x inputs pub state addr outside names X endAddr savedScratch incoming good start fit
    values resident hist directory es
  have run : (run src dst (baseDemand B i.1) I.demand G (basePayload B) (lookup B i.1)
      (selectorTable B) (selectorCode B) I.payload i.2 d x).1.isSome = true := by
    simpa only [names, i, runEntry, Option.isSome_map] using good
  obtain ⟨θ, selected, valid⟩ := MapScratch.sequence_of_success run
  let V := F.placement pc own advance i
  obtain ⟨writer, body, done, _⟩ := F.links pc dfs saved common own advance M installed i
  obtain ⟨out, pre, len, reads, choice, exit, per, regs, memory, histogram, post, _⟩ :=
    MapArgumentWriter.written_success_exact hp I L F.ordinal V (F.base i) (F.field i) X (F.vm own i)
      inputs (F.aux own i) (F.writerPC pc i) M writer (F.vm_safe dfs saved common own banks i)
      (F.vm_aux own i) (F.pointer pc own advance i) body hw c m start fit values resident
      hist directory θ selected valid
  have trace : es = MapArgumentWriter.events (F.base i) (F.fields i) pub state m ++
      List.replicate (MapInline.factor L F.ordinal * entryTicks hp I L F.ordinal hw θ) .tick := by
    exact congrArg (fun pick : Option (Fin (repetitions B I.demand) → Selector B) ↦
      MapArgumentWriter.events (F.base i) (F.fields i) pub state m ++
        List.replicate (MapInline.factor L F.ordinal * pick.elim 0 (entryTicks hp I L F.ordinal hw))
          (.tick : Event w)) selected
  rw [trace]
  refine ⟨out, pre, len, reads, choice, exit.trans done, per, ?_, memory, histogram, ?_⟩
  · intro q apart
    apply regs q
    · apply InlinePublic.linked_privateReg
      rintro ⟨v, eq⟩
      exact apart (.inr (.inr v)) eq.symm
    · exact fun v ↦ apart (.inl v)
    · intro v
      fin_cases v <;> exact apart _
  · exact MapScratch.exact_upper L.core L.args (L.corePC L.locations) X addr
      (selectorWord B (fits_of_threshold B hw).2.2.2) F.ordinal endAddr savedScratch
      incoming run post

include installed banks in
/-- Both branches of the selected action run on the actual linked image.
A missing entry rejects every fuel bound and incoming choice stream. -/
theorem action_native (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (hw : widthThreshold B ≤ w) (c : Config w p r) (m : Memory w) :
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
    ∀ (X : MapEntry.Program.Workspace (MapInline.callProgram L) I.demand I.payload d x t w)
      (endAddr : ℕ) (savedScratch : DFS.Scratch w endAddr),
      DFS.scratch endAddr c.privateMem = savedScratch →
      c.pc = F.target pc i →
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w →
      (∀ a, (F.field i a).eval pub state m =
        MapCallSetup.values L.core (L.corePC L.locations) X a) →
      MapArgumentWriter.ResidentFields L.core (L.corePC L.locations) X addr c.privateMem →
      (∀ l : Fin t, outside ((X.hist + l.val : ℕ) : BurstRAM.Word w)) →
      (∀ (l : Fin t) (j : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (j.val : BurstRAM.Word w)) →
      match F.action hp I hw pub state m X endAddr savedScratch with
      | none => ∀ bs, ¬ DFS.Returns M c m bs
      | some (es, updated) => ∃ out, NodeArguments.ChildScan.Prefix M m c out [] es ∧
          out.pc = advance ∧ out.persistent = c.persistent ∧
          (∀ q, (∀ a : F.Local i, q ≠ F.localReg own i a) → out.reg q = c.reg q) ∧
          (∀ q, outside q → MapCallSetup.Outside L.core (L.corePC L.locations) X q →
            out.privateMem q = c.privateMem q) ∧
          (∀ l : Fin t, out.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
            c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) +
              ((names.getD []).count l : BurstRAM.Word w)) ∧
          DFS.scratch endAddr out.privateMem = updated := by
  intro i L d x inputs pub state addr outside names X endAddr savedScratch incoming start fit
    values resident hist directory
  cases got : F.action hp I hw pub state m X endAddr savedScratch with
  | none =>
    have miss := (F.action_none_iff hp I hw pub state m X endAddr savedScratch).mp got
    obtain ⟨out, es, pre, _, _, _, exit, _⟩ := F.native pc dfs saved common own advance M
      installed banks hp I hw c m X start fit values resident hist directory
    have reject : M.code out.pc = .reject := by
      simpa only [miss, Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        using exit
    intro bs returns
    obtain ⟨fuel, rep, ran⟩ := (pre.returns bs).mp returns
    have step : M.program.step out = .reject := by
      change (M.code out.pc).run M.publicData out = _
      rw [reject]
      rfl
    cases fuel <;> simp only [execute, step, reduceCtorEq] at ran
  | some pair =>
    obtain ⟨es, updated⟩ := pair
    obtain ⟨ok, trace, final⟩ :=
      (F.action_some_iff hp I hw pub state m X endAddr savedScratch).mp got
    have good : names.isSome = true := by simpa only [names, Option.isSome_map] using ok
    obtain ⟨out, pre, _, _, _, endPC, per, regs, mem, counts, scratch⟩ :=
      F.native_success_exact pc dfs saved common own advance M installed banks hp I hw c m X
        endAddr savedScratch incoming good start fit values resident hist directory
    exact ⟨out, trace ▸ pre, endPC, per, regs, mem, counts, scratch.trans final.symm⟩

end PairSimulation.MapHandlerImage.Family

end VPVNP
end Computability
end OAI
