import OAI.Computability.VPVNP.PairSimulationMapInline

/-!
# Private memory after an inlined motif map call

Lowering the public constants changes the register allocation and instruction count.
The host uses the source call's private memory, so its output satisfies the same
canonical update of the directory, selector, label and histogram cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifDemandPadding
open BurstRAM.PrivateRAM PrimedCounter.GuessWord InlinePublic
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k t w P R : ℕ}

namespace MapConstants

variable (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
  (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)
  (ord : (parameterData B).Entry → Fin t)

/-- Installing the cast of the fixed natural constant bank preserves the
canonical private-memory update of the full descriptor-driven map. -/
theorem source_run_post (hw : widthThreshold B ≤ w) :
    let loc := L.corePC L.locations
    let A := L.core.program loc
    let M := source (w := w) L ord
    let demand := MotifEntry.demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ MotifEntry.inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace A I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      MapCallSetup.Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      A.RunsPost M c X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord))
        (MapCallSetup.Success L.core loc X (selectorWord B (fits_of_threshold B hw).2.2.2)
          ord c.privateMem) := by
  obtain ⟨fb, fd, fs, hs⟩ := fits_of_threshold B hw
  have run := MapCallTable.Layout.run_entryInput_post hp I L fb (fd _) fs (selectorWord B hs) ord
  rw [installed_eq_cast L.core ord fb (fd _) fs hs] at run
  exact run

end MapConstants

namespace MapInline

open MapConstants

variable (L : MapCallTable.Layout B z j r k) (ord : (parameterData B).Entry → Fin t)
  (V : Placement (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r P R)
  (M : Machine w P R 11)

/-- The call returns its exit, histogram, preserved caller state and private-memory
postcondition on a single host instruction path. -/
def RunsPost (h : Config w P R) (hist cap : ℕ) (save : BurstRAM.Word w → Prop)
    (result : Option (List (Fin t))) (post : PrivateScratch.Memory w → Prop) : Prop :=
  ∃ n out, n ≤ factor L ord * cap ∧ Prefix M h (List.replicate n .tick) out ∧
    out.persistent = h.persistent ∧ (∀ i, V.privateReg i → out.reg i = h.reg i) ∧
    (∀ a, save a → out.privateMem a = h.privateMem a) ∧
    Outcome hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done) h out result ∧
    post out.privateMem

/-- An individual source prefix of length `n` has exactly `factor L ord * n` host ticks.
Its private postcondition holds on the same host state as its register and histogram effects. -/
theorem lift_path_post (linked : Linked L ord V M) (h : Config w P R)
    (pc : h.pc = V.entry L.template.entry)
    {hist n : ℕ} {result : Option (List (Fin t))} {save : BurstRAM.Word w → Prop}
    {post : PrivateScratch.Memory w → Prop} {last : Config w (Nat.card L.Address) r}
    (pre : Prefix (source (w := w) L ord) (restrict V L.template.entry h)
      (List.replicate n .tick) last)
    (persistent : last.persistent = h.persistent)
    (saved : ∀ a, save a → last.privateMem a = h.privateMem a)
    (effect : (callProgram L).Effect (restrict V L.template.entry h) last hist result)
    (ok : post last.privateMem) :
    ∃ out, Prefix M h (List.replicate (factor L ord * n) .tick) out ∧
      out.persistent = h.persistent ∧ (∀ i, V.privateReg i → out.reg i = h.reg i) ∧
      (∀ a, save a → out.privateMem a = h.privateMem a) ∧
      Outcome hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done) h out result ∧
      post out.privateMem := by
  obtain ⟨out, pref, rel⟩ := ticks_lower L.template (rawBank L.core ord) V M
    (operand_le L.template (rawBank L.core ord)) linked pre (restrict_related V _ h pc)
  refine ⟨out, pref, rel.1.persistent.trans persistent, rel.1.frame,
    fun a ha ↦ (congrFun rel.1.privateMem a).trans (saved a ha), ?_, rel.1.privateMem ▸ ok⟩
  cases result with
  | none | some _ =>
    refine ⟨rel.2.trans (congrArg V.entry effect.1), fun i ↦ ?_⟩
    rw [rel.1.privateMem]
    exact effect.2 i

/-- Lower the complete source call, retaining its postcondition and multiplying its
instruction bound by the fixed block length. -/
theorem lift_run_post (linked : Linked L ord V M) (h : Config w P R)
    (pc : h.pc = V.entry L.template.entry) {hist cap : ℕ} {result : Option (List (Fin t))}
    {save : BurstRAM.Word w → Prop} {post : PrivateScratch.Memory w → Prop}
    (path : (callProgram L).RunsPost (source (w := w) L ord) (restrict V L.template.entry h)
      hist cap save result post) : RunsPost L ord V M h hist cap save result post := by
  obtain ⟨n, last, bound, pre, per, frame, effect, ok⟩ := path.path
  obtain ⟨out, facts⟩ := lift_path_post L ord V M linked h pc pre per frame effect ok
  exact ⟨factor L ord * n, out, Nat.mul_le_mul_left _ bound, facts⟩

/-- Run the inlined map from the caller's resident descriptor. The canonical memory
update uses the same initial host memory and the same exit as the histogram result. -/
theorem run_entryInput_post (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)
    (V : Placement (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r P R)
    (M : Machine w P R 11) (linked : Linked L ord V M) (hw : widthThreshold B ≤ w) :
    let loc := L.corePC L.locations
    let demand := MotifEntry.demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ MotifEntry.inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace (callProgram L) I.demand I.payload demand supply t w)
      (h : Config w P R), h.pc = V.entry L.template.entry →
      MapCallSetup.Input L.core L.args loc X L.ptr (restrict V L.template.entry h) →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      RunsPost L ord V M h X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord))
        (MapCallSetup.Success L.core loc X (selectorWord B (fits_of_threshold B hw).2.2.2)
          ord h.privateMem) := by
  intro loc demand supply X h pc input apart
  exact lift_run_post L ord V M linked h pc (source_run_post hp I L ord hw X _ rfl input apart)

end MapInline

end PairSimulation

end VPVNP
end Computability
end OAI
