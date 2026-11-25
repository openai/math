import OAI.Computability.MultitapeWeakETH.HistoryKernelLevel
import OAI.Computability.MultitapeWeakETH.HistoryShrinkReader
import OAI.Computability.MultitapeWeakETH.HistoryRefresh
import OAI.Computability.MultitapeWeakETH.ResidentHistory

/-! # Uniform kernel dispatch on an entire retained branch -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif Compression.DegreeRefresh
open Compression.Refresh CompressorRecords NetworkKernel PairSimulation LocalHistory NodeArguments TraversalRows
open PortRefresh RefreshMapOperands ShrinkBlockInputs ShrinkMap DyadicBudget
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  {hist : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → R) (hf : B.IsSolution f)

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

private theorem shrinking (i : Fin S.steps) :
    ∃ run : Kernel, Poly run ∧ ∃ N : ℕ, ∀ (H : ResidentHistory B f hf), N ≤ gridIndex B H.volume →
      ∀ (j : Fin H.passes.length) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
        (sel : SelectedScore.Selection B X) (tape : List Bool),
        H.passes[j.val] = shrinkLevel B f hf i X sel tape →
        LevelKernelSpec order f hf (shrinkLevel B f hf i X sel tape) (gridWidth B H.volume) (H.point j.val) run := by
  obtain ⟨run,cost,N,h⟩ := history_shrink_read B i (fun l => (order (.inl l)).val) f hf
  refine ⟨run,cost,N,?_⟩
  intro H room j g X sel tape chosen
  apply shrink_level_spec
  intro z occurrence args
  apply shrink_kernel_spec order f hf z
  intro bits labels tail
  exact h H.volume room H.path H.log H.stored j z tape (chosen.trans occurrence) bits tail labels

local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

private theorem refreshing :
    ∃ run : RefreshQuery → Option (List Tally), Poly run ∧ ∀ (H : ResidentHistory B f hf),
      max 1 (slotDegree S) ≤ gridIndex B H.volume →
      ∀ (j : Fin H.passes.length) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
        (c : DyadicRefreshChoice (a₀:=S.degreeExponent 0) X S.graph hE hC B.refresh) (tape : List Bool),
        H.passes[j.val] = RefreshPlacement.selectedLevel B f hf X c tape →
        LevelKernelSpec order f hf (RefreshPlacement.selectedLevel B f hf X c tape) (gridWidth B H.volume)
          (H.point j.val) (refreshKernel run) := by
  obtain ⟨run,cost,h⟩ := history_refresh B order f hf
  refine ⟨run,cost,?_⟩
  intro H room j g X c tape chosen
  apply refresh_level_spec
  exact h H.volume ((le_max_left ..).trans room) ((le_max_right ..).trans room) H.path H.log H.stored j X c tape chosen

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
/-- Finite schedule thresholds are uniform in the history, site, private stream
and level index. Every physical dispatch returns the scheduled word and exponents. -/
theorem history_kernels :
    ∃ (sh : Fin S.steps → Kernel) (refresh : RefreshQuery → Option (List Tally)),
      (∀ i, Poly (sh i)) ∧ Poly refresh ∧ ∃ N : ℕ, ∀ H : ResidentHistory B f hf, N ≤ gridIndex B H.volume →
      ∀ j : Fin H.passes.length, LevelKernelSpec order f hf H.passes[j.val] (gridWidth B H.volume) (H.point j.val)
        (fun q => dispatch sh (refreshKernel refresh) (tally j.val,q)) := by
  choose sh hp stageN good using shrinking B order f hf
  obtain ⟨refresh,rp,fresh⟩ := refreshing B order f hf
  let bound := Finset.univ.sup stageN
  refine ⟨sh,refresh,hp,rp,max (max 1 (slotDegree S)) bound,?_⟩
  intro H large j
  let V := H.passes[j.val]
  let active (v : SelectedLevel B f hf) : Kernel :=
    if h : v.origin.ordinal < S.steps then sh ⟨_,h⟩ else refreshKernel refresh
  have eqn : (fun q => dispatch sh (refreshKernel refresh) (tally j.val,q)) = active V := by
    funext q
    have eval := dispatch_origin B f hf _ (lanes_fit B _) _ H.path sh (refreshKernel refresh) j q
    change _ = (if h : V.origin.ordinal < S.steps then sh ⟨_,h⟩ q else refreshKernel refresh q) at eval
    by_cases h : V.origin.ordinal < S.steps <;> simpa only [active,h,↓reduceDIte] using eval
  rw [eqn]
  suffices every : ∀ v : SelectedLevel B f hf, V = v →
      LevelKernelSpec order f hf v (gridWidth B H.volume) (H.point j.val) (active v) from every V rfl
  rintro ⟨a,g,b,n,X,pass,origin,term,tape⟩ occurrence
  cases origin with
  | shrink i length X =>
    subst g
    have fits : stageN i ≤ bound := Finset.le_sup (f:=stageN) (Finset.mem_univ i)
    have atSite := good i H (fits.trans ((le_max_right ..).trans large)) j X term tape occurrence
    change LevelKernelSpec order f hf (shrinkLevel B f hf i X term tape) _ _
      (if h : i.val < S.steps then sh ⟨i.val,h⟩ else refreshKernel refresh)
    simpa only [i.isLt,↓reduceDIte] using atSite
  | refresh X =>
    have atSite := fresh H ((le_max_left ..).trans large) j X term tape occurrence
    change LevelKernelSpec order f hf (RefreshPlacement.selectedLevel B f hf X term tape) _ _
      (if h : S.steps < S.steps then sh ⟨S.steps,h⟩ else refreshKernel refresh)
    simpa only [lt_irrefl,↓reduceDIte] using atSite

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
