import OAI.Computability.BorderVNP.PackedBankCompiledScalars
import OAI.Computability.BorderVNP.PackedBankFullHistory

/-! # The three terminal compiler bounds from a selected machine's bottom programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing Inherited PhysicalEpochs EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : SiteSchedule e} {start T : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {w np : ℕ} (C : Compiled bits deep budget cap w) (leaf : P ↪ Fin np)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ) (bottom : Admissible
      (Boundary.Good (S := S) (start := start) (bits := bits) (shape := boundaryShape S start) (w := w) budget) 0)
    (base : Site.Programs bottom.val.pack.layout)

/-- The selected terminal compiler has a small public load, a separate full stored
load and a local scalar limit on every actual site. -/
theorem Compiled.terminalCompilerCaps (hm : 0 < m) (Bpub Bfull U₀ : ℕ)
    (pub : SiteCap bottom.val.route base.bankFields false Bpub)
    (full : SiteCap bottom.val.route base.fullFields true Bfull)
    (scalar : ∀ v, let s := (base v).program
      s.ScalarBound (max U₀ (max 1 s.size))) (q : (packHistory bottom C.machine.epoch T).Index)
    (code : (Cube D → Deck (depth S start T+1)) ↪ ℕ) (c : ℕ) :
    let state := ((packHistory bottom C.machine.epoch T).term q).val
    let N := (flattenPack T state.pack).layout
    let pr := C.machine.terminalPrivatePrograms (C.privateSiteRows leaf seeds) number bottom base q
    let owner := fun v => code (reduceMove (depth S start T) (state.route.origin v))
    let L := S.publicProgramFactor^T*Bfull
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    1+FinalCell.publicLoad N owner (fun v => (pr v).program) c ≤ S.publicProgramFactor^T*Bpub ∧
    (∀ ex, 1+localRecords N ex (fun v => (pr v).program.staticNodes) (fun v => (pr v).program.expandedLoad)
      (fun v => owner v=c) ≤ L) ∧
    ∀ v, (pr v).program.ScalarBound (max U₀ (coeff*(L+1))) := by
  intro state N pr owner L coeff
  have expanded : SiteCap bottom.val.route base.bankFields true Bfull := by
    intro tile
    have fit := bankRecords_le bottom.val.pack.layout base base.fullFields true (fun v => ⟨(base v).program.publicNodes_le_staticNodes,le_rfl⟩)
      (fun v => reduceMove (depth S start 0) (bottom.val.route.origin v) = tile)
    exact (Nat.add_le_add_left fit 1).trans (full tile)
  exact ⟨C.machine.terminalPrivatePrograms_publicLoad (C.privateSiteRows leaf seeds) number bottom base Bpub pub q code c,
    fun ex => C.machine.terminalPrivatePrograms_fullLoad (C.privateSiteRows leaf seeds) number bottom base Bfull full q code c ex,
    C.terminalPrivatePrograms_localScalars_of_extent leaf seeds number bottom base hm Bfull U₀ expanded scalar q⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
