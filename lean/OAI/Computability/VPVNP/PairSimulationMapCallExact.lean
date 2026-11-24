import OAI.Computability.VPVNP.PairSimulationMapEntryExact
import OAI.Computability.VPVNP.PairSimulationMapPost
import OAI.Computability.VPVNP.PairSimulationTickTerminal

/-!
# Exact successful clock of an initialized and inlined motif map

The register recipes and the pointer directory add a fixed prefix to the successful
map evaluation. Inlining the public constants then multiplies the length of this
entire prefix by the block length. The host reaches its successful continuation with
the same private memory as the source computation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifDemandPadding MotifEntry
open BurstRAM.PrivateRAM PrimedCounter.GuessWord InlinePublic MapEntryTable
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {r k t w P R : ℕ}

namespace MapConstants

variable (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
  (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)
  (ord : (parameterData B).Entry → Fin t)

local notation "loc" => L.corePC L.locations
local notation "d" => demandBits src dst I.party I.demandBits
local notation "x" => mapHalf G (fun _ ↦ inputBits) I.supplyBits
local notation "u" => repetitions B I.demand

/-- Source tick count at the given selector sequence, including both initializer phases. -/
noncomputable def entryTicks (hw : widthThreshold B ≤ w) (θ : Fin u → Selector B) : ℕ :=
  L.lines.length + (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
    (MapInline.callProgram L).successTicks d x θ ((fits_of_threshold B hw).2.1 _)
      (fits_of_threshold B hw).2.2.1 (source (w := w) L ord).publicData

/-- The fixed natural public bank runs the initialized map for exactly its successful
tick count. The memory equality includes the directory written by initialization. -/
theorem source_run_success_exact (hw : widthThreshold B ≤ w)
    (X : MapEntry.Program.Workspace (MapInline.callProgram L) I.demand I.payload d x t w)
    (c : Config w (Nat.card L.Address) r) (pc : c.pc = (source (w := w) L ord).entry)
    (input : MapCallSetup.Input L.core L.args loc X L.ptr c)
    (θ : Fin u → Selector B)
    (selected : (selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1 = some θ)
    (valid : ∀ e, I.payload e = totalWidth (basePayload B) θ e) :
    let ticks := entryTicks hp I L ord hw θ
    ∃ out, ticks ≤ L.lines.length + (1 + 3 * (MapPortAgreement.ports G I.party
        L.core.edgeOrder).length) + MapNativeClock.cap B (demandGrid B hp I.demand) I.party u ∧
      Prefix (source (w := w) L ord) c (List.replicate ticks .tick) out ∧
      out.pc = (MapInline.callProgram L).done ∧ out.persistent = c.persistent ∧
      out.privateMem = (MapInline.callProgram L).successMemory X
        (selectorWord B (fits_of_threshold B hw).2.2.2) ord θ
        (MapCallSetup.directoryMemory L.core loc X c.privateMem) := by
  let M := source (w := w) L ord
  let P₀ := MapInline.callProgram L
  obtain ⟨fb, fd, fs, hs⟩ := fits_of_threshold B hw
  let sel := selectorWord B hs
  have pub (a : MapEntryTable.PublicPort B (demandGrid B hp I.demand) I.party) :
      M.publicData (L.core.pub a) = Allocation.words fb (fd _) fs sel
        (fun e ↦ ((ord e).val : BurstRAM.Word w)) a := by
    change (rawBank L.core ord (L.core.pub a) : BurstRAM.Word w) = _
    rw [rawBank_at, words_eq_cast]
  obtain ⟨init, dir, core⟩ := L.links L.locations M (fun a _ ↦ L.template_at _ a)
  obtain ⟨m, first, ready, persistent, outside⟩ :=
    MapCallSetup.native L.core L.args loc X L.slots M L.ptr L.scratch L.directoryApart
      (L.dirPC L.locations) dir L.vm L.output L.vmApart (L.initPC L.locations) init
      (by simp [MapCallTable.Layout.initPC]) c pc input
  have directory : m.privateMem = MapCallSetup.directoryMemory L.core loc X c.privateMem :=
    PrivateScratch.eq_write _ _ ready.selector.resident.pointers outside
  obtain ⟨out, bound, tail, done, keep, written⟩ :=
    P₀.native_success_exact X M (L.core.linked loc M core) (L.core.separate loc)
      sel ord fb (fd _) fs (L.core.public_spec loc fb (fd _) fs sel _ M pub) m ready
      θ selected valid
  refine ⟨out, Nat.add_le_add_left bound _, ?_, done, keep.trans persistent, ?_⟩
  · rw [entryTicks, List.replicate_add]
    exact first.append tail
  · rw [written, directory]

end MapConstants

namespace MapInline

open MapConstants

variable (ord : (parameterData B).Entry → Fin t) (hp : ∀ e, 0 < p₀ e)
  (I : LocalHistory.EntryInput B)
  (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)

local notation "loc" => L.corePC L.locations
local notation "d" => demandBits src dst I.party I.demandBits
local notation "x" => mapHalf G (fun _ ↦ inputBits) I.supplyBits
local notation "u" => repetitions B I.demand

/-- Transport the exact successful source path and its canonical private memory to
the host. The caller's registers, exterior memory and histogram are framed on that path. -/
theorem run_entryInput_success_exact
    (V : Placement (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r P R)
    (M : Machine w P R 11) (linked : Linked L ord V M) (hw : widthThreshold B ≤ w)
    (X : MapEntry.Program.Workspace (callProgram L) I.demand I.payload d x t w)
    (h : Config w P R) (pc : h.pc = V.entry L.template.entry)
    (input : MapCallSetup.Input L.core L.args loc X L.ptr (restrict V L.template.entry h))
    (apart : ∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w))
    (θ : Fin u → Selector B)
    (selected : (selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1 = some θ)
    (valid : ∀ e, I.payload e = totalWidth (basePayload B) θ e) :
    let ticks := factor L ord * entryTicks hp I L ord hw θ
    let sel := selectorWord B (fits_of_threshold B hw).2.2.2
    let names := (runEntry B hp I.demand I.payload I.party d x).1.map (List.map ord)
    ∃ out, ticks ≤ factor L ord * (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party u) ∧
      Prefix M h (List.replicate ticks .tick) out ∧ out.persistent = h.persistent ∧
      (∀ i, V.privateReg i → out.reg i = h.reg i) ∧
      (∀ a, MapCallSetup.Outside L.core loc X a → out.privateMem a = h.privateMem a) ∧
      Outcome X.hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done) h out names ∧
      MapCallSetup.Success L.core loc X sel ord h.privateMem out.privateMem ∧
      out.pc = V.entry (callProgram L).done ∧
      out.privateMem = (callProgram L).successMemory X sel ord θ
        (MapCallSetup.directoryMemory L.core loc X h.privateMem) := by
  intro ticks sel names
  let c := restrict V L.template.entry h
  let S := source (w := w) L ord
  obtain ⟨last, bound, pre, done, per, memory⟩ :=
    source_run_success_exact hp I L ord hw X c rfl input θ selected valid
  obtain ⟨n, other, _, otherPre, _, save, effect, post⟩ :=
    (source_run_post hp I L ord hw X c rfl input apart).path
  have accept (s : Config w (Nat.card L.Address) r) (hs : s.pc = (callProgram L).done) :
      S.program.step s = .finish none := by
    change ((L.template.code s.pc).resize w).run _ s = _
    rw [hs, (exit_codes L).2]
    rfl
  have terminal : S.program.step other = .reject ∨
      ∃ result, S.program.step other = .finish result := by
    change (callProgram L).Effect c other X.hist names at effect
    cases hn : names with
    | none =>
      rw [hn] at effect
      left
      change ((L.template.code other.pc).resize w).run _ other = _
      rw [effect.1, (exit_codes L).1]
      rfl
    | some _ =>
      rw [hn] at effect
      exact Or.inr ⟨none, accept _ effect.1⟩
  obtain ⟨_, rfl⟩ := Prefix.ticks_terminal_unique pre otherPre (Or.inr ⟨none, accept _ done⟩)
    terminal
  obtain ⟨out, pref, rel⟩ := ticks_lower L.template (rawBank L.core ord) V M
    (operand_le L.template (rawBank L.core ord)) linked pre (restrict_related V _ h pc)
  refine ⟨out, Nat.mul_le_mul_left _ bound, pref, rel.1.persistent.trans per, rel.1.frame,
    fun a ha ↦ (congrFun rel.1.privateMem a).trans (save a ha), ?_, rel.1.privateMem ▸ post,
    rel.2.trans (congrArg V.entry done), rel.1.privateMem.trans memory⟩
  change (callProgram L).Effect c last X.hist names at effect
  cases hn : names with
  | none | some _ =>
    rw [hn] at effect
    refine ⟨rel.2.trans (congrArg V.entry effect.1), fun i ↦ ?_⟩
    rw [rel.1.privateMem]
    exact effect.2 i

end MapInline

end PairSimulation

end VPVNP
end Computability
end OAI
