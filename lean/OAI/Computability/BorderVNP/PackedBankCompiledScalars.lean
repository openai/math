import OAI.Computability.BorderVNP.PackedBankPrivateScalarHistory
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows

/-! # Terminal scalar fields on the selected physical machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing Inherited PublicCapacity EnrichedOuter
  PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {w np : ℕ} (C : Compiled bits deep budget cap w)

/-- Every active epoch of the selected processor obtains its measurement from
the original installed normalized node and its actual input tuple. -/
theorem Compiled.machine_measures (t : ℕ) (ht : t<T) : (C.machine t ht).Measures :=
  fun i c => ((C.atLevel t ht).program.installed i c).measure

variable (leaf : P ↪ Fin np) (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ) (bottom : Admissible
      (Boundary.Good (S := S) (start := start) (bits := bits) (shape := boundaryShape S start) (w := w) budget) 0)
    (base : Site.Programs bottom.val.pack.layout)

/-- Raw local fields of the terminal private program using the selected machine's
native site, cable, and port numbering. The tile and scalar caps at the bottom
are the sole data-dependent premises. -/
theorem Compiled.terminalPrivatePrograms_localScalars (hm : 0 < m) (B U₀ : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B) (hbase : ∀ v, (base v).program.ScalarBound U₀)
    (q : (packHistory bottom C.machine.epoch T).Index) (v) :
    let L := S.publicProgramFactor^T*B
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    (C.machine.terminalPrivatePrograms (C.privateSiteRows leaf seeds) number bottom base q v).program.ScalarBound
      (max U₀ (coeff*(L+1))) :=
  C.machine.terminalPrivatePrograms_localScalars (C.privateSiteRows leaf seeds) number bottom base hm C.machine_measures
    B U₀ hcap hbase q v

/-- The extent-sensitive finite-grid bottom invariant also gives the same terminal
word bound on the actual selected machine. -/
theorem Compiled.terminalPrivatePrograms_localScalars_of_extent (hm : 0 < m) (B U₀ : ℕ)
    (hcap : SiteCap bottom.val.route base.bankFields true B) (hbase : ∀ v, let s := (base v).program
      s.ScalarBound (max U₀ (max 1 s.size)))
    (q : (packHistory bottom C.machine.epoch T).Index) (v) :
    let L := S.publicProgramFactor^T*B
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    (C.machine.terminalPrivatePrograms (C.privateSiteRows leaf seeds) number bottom base q v).program.ScalarBound
      (max U₀ (coeff*(L+1))) :=
  C.machine.terminalPrivatePrograms_localScalars_of_extent (C.privateSiteRows leaf seeds) number bottom base hm C.machine_measures
    B U₀ hcap hbase q v

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
