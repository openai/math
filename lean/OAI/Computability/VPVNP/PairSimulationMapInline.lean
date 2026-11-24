import OAI.Computability.VPVNP.PairSimulationMapConstants
import OAI.Computability.VPVNP.PairSimulationInlinePrefix

/-!
# A reusable motif map on the eleven public input words

The installed body obtains every fixed selector and label constant from its
instructions. Its two exit labels can be the enclosing continuation and
failure labels. A successful call increments the resident histogram exactly
once per output label. A failed call preserves every histogram cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapInline

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifDemandPadding
open BurstRAM.PrivateRAM PrimedCounter.GuessWord InlinePublic MapConstants
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k t w P R : ℕ}
  (L : MapCallTable.Layout B z j r k) (ord : (parameterData B).Entry → Fin t)

/-- The slowdown per source instruction, fixed for the entire role and grid point. -/
noncomputable def factor := capacity L.template (rawBank L.core ord) + 3

/-- The standalone fixed map table, ready to instantiate with the actual eleven words. -/
noncomputable def template11 : Template (Nat.card L.Address * factor L ord) (r + 2) 11 :=
  compiled 11 L.template (rawBank L.core ord)

/-- Grouped entry program at the core instruction addresses of the numbered call table. Its
success and failure labels identify the exits to relocate when inlining the table. -/
noncomputable abbrev callProgram := L.core.program (L.corePC L.locations)

theorem exit_codes :
    L.template.code (callProgram L).bad = .reject ∧
      L.template.code (callProgram L).done = .accept := by
  simp [MapCallTable.Layout.template, callProgram, MapEntryTable.Allocation.program,
    MapCallTable.Layout.corePC, MapEntryTable.Allocation.exitPC, MapCallTable.Layout.text,
    MapEntryTable.Allocation.text]

/-- Exact private histogram and the continuation reached in the enclosing machine. -/
def Outcome {p r : ℕ} (hist : ℕ) (bad done : Fin p) (c out : Config w p r) :
    Option (List (Fin t)) → Prop
  | none => out.pc = bad ∧ ∀ l : Fin t,
      out.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) =
      c.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w)
  | some names => out.pc = done ∧ ∀ l : Fin t,
      out.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) =
      c.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) + (names.count l : BurstRAM.Word w)

variable (V : Placement (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r P R)
  (M : Machine w P R 11)

/-- Instruction-level installation requires only the body between the exits. -/
def Linked : Prop := ∀ pc, continues (L.template.code pc) = true →
  ContainsAt M L.template (rawBank L.core ord) V pc

/-- A fully framed host path from a restricted initial configuration. -/
def Runs (h : Config w P R) (hist cap : ℕ) (result : Option (List (Fin t))) : Prop :=
  ∃ n out, n ≤ factor L ord * cap ∧ Prefix M h (List.replicate n .tick) out ∧
    out.persistent = h.persistent ∧ (∀ i, V.privateReg i → out.reg i = h.reg i) ∧
    Outcome hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done) h out result

/-- The exact host path, including all private cells saved by the complete map call. -/
def RunsFramed (h : Config w P R) (hist cap : ℕ) (save : BurstRAM.Word w → Prop)
    (result : Option (List (Fin t))) : Prop :=
  ∃ n out, n ≤ factor L ord * cap ∧ Prefix M h (List.replicate n .tick) out ∧
    out.persistent = h.persistent ∧ (∀ i, V.privateReg i → out.reg i = h.reg i) ∧
    (∀ a, save a → out.privateMem a = h.privateMem a) ∧
    Outcome hist (V.entry (callProgram L).bad) (V.entry (callProgram L).done) h out result

theorem RunsFramed.forget {h : Config w P R} {hist cap : ℕ} {save : BurstRAM.Word w → Prop}
    {value : Option (List (Fin t))} (run : RunsFramed L ord V M h hist cap save value) :
    Runs L ord V M h hist cap value := by
  obtain ⟨n, out, cap, path, per, reg, _, endAt⟩ := run
  exact ⟨n, out, cap, path, per, reg, endAt⟩

/-- Transport the concrete source call without using any of the caller's public words. -/
theorem lift_run_framed (linked : Linked L ord V M) (h : Config w P R)
    (pc : h.pc = V.entry L.template.entry)
    {hist cap : ℕ} {result : Option (List (Fin t))}
    {save : BurstRAM.Word w → Prop}
    (path : (callProgram L).RunsFramed (source (w := w) L ord) (restrict V L.template.entry h)
      hist cap save result) : RunsFramed L ord V M h hist cap save result := by
  obtain ⟨n, last, hn, pre, keep, saved, endAt⟩ := path.path
  obtain ⟨out, pref, rel⟩ := ticks_lower L.template (rawBank L.core ord) V M
    (operand_le L.template (rawBank L.core ord)) linked pre (restrict_related V _ h pc)
  refine ⟨factor L ord * n, out, Nat.mul_le_mul_left _ hn, pref, rel.1.persistent.trans keep,
    rel.1.frame, fun a ha ↦ (congrFun rel.1.privateMem a).trans (saved a ha), ?_⟩
  cases result with
  | none =>
    refine ⟨rel.2.trans (congrArg V.entry endAt.1), fun i ↦ ?_⟩
    rw [rel.1.privateMem]
    exact endAt.2 i
  | some names =>
    refine ⟨rel.2.trans (congrArg V.entry endAt.1), fun i ↦ ?_⟩
    rw [rel.1.privateMem]
    exact endAt.2 i

/-- The full map from a resident raw descriptor to the enclosing histogram.
The eleven public input words are arbitrary. -/
theorem run_entryInput_framed (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
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
      RunsFramed L ord V M h X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro loc demand supply X h pc input apart
  exact lift_run_framed L ord V M linked h pc (source_run_framed hp I L ord hw X _ rfl input apart)

/-- The full map from a resident raw descriptor to the enclosing histogram.
The eleven public input words are arbitrary. -/
theorem run_entryInput (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
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
      Runs L ord V M h X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro loc demand supply X h pc input apart
  exact (run_entryInput_framed ord hp I L V M linked hw X h pc input apart).forget L ord V M

/-- The canonical finite code discharges every installation condition. -/
theorem template11_linked (pub : Fin 11 → BurstRAM.Word w) :
    Linked L ord (canonical (capacity L.template (rawBank L.core ord)) (Nat.card L.Address) r)
      ((template11 L ord).instantiate w pub) :=
  fun pc _ ↦ compiled_contains L.template (rawBank L.core ord) pub pc

/-- One constant works for all grid points, parties, repetitions and word widths.
It includes expression initialization, the private directory, and the inlined constants. -/
theorem uniform {rr kk : B.grid.demands → J → ℕ}
    (layouts : ∀ z j, MapCallTable.Layout B z j (rr z j) (kk z j)) :
    ∃ A : ℕ, ∀ z j u, factor (layouts z j) ord *
      ((layouts z j).lines.length + (1 + 3 *
        (MapPortAgreement.ports G j (layouts z j).core.edgeOrder).length) +
        MapNativeClock.cap B z j u) ≤ A * (u + 1) := by
  obtain ⟨C, hC⟩ := MapNativeClock.uniform B
  let start := fun z j ↦ (layouts z j).lines.length +
    (1 + 3 * (MapPortAgreement.ports G j (layouts z j).core.edgeOrder).length)
  let weight := fun z j ↦ factor (layouts z j) ord * (start z j + C)
  refine ⟨∑ z : B.grid.demands, ∑ j, weight z j, fun z j u ↦ ?_⟩
  have hweight := (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (weight z i))
    (Finset.mem_univ j)).trans (Finset.single_le_sum (fun a _ ↦ Nat.zero_le (∑ i, weight a i))
      (Finset.mem_univ z))
  have hstart := Nat.le_mul_of_pos_right (start z j) (Nat.succ_pos u)
  calc
    _ ≤ factor (layouts z j) ord * ((start z j + C) * (u + 1)) := by
      rw [Nat.add_mul]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add hstart (hC z j u))
    _ = weight z j * (u + 1) := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hweight

end PairSimulation.MapInline

end VPVNP
end Computability
end OAI
