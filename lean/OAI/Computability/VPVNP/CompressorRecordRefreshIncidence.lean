import OAI.Computability.VPVNP.CompressorRecordRefreshAllSlots
import OAI.Computability.VPVNP.CompressorRecordRefreshBaseOutput
import OAI.Computability.VPVNP.CompressorRecordRefreshInputs

/-!
# The six incidence columns after degree refresh

The selected supply widths and completed external bundles feed every numbered actual slot
writer. A final pass reads the outgoing arcs on lane zero and recovers the base permutation,
its inverse and its residual-lane shifts. The output is the common directory expected by the
next shrinking pass, at the precise state selected by this term of the refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry

variable {bits a a₀ g dH : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)
  (I : AllSlots.Tables bits) (T : IncidenceDirectory bits) (mem : Memory bits)

local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice
local notation "N" => Fintype.card X.Base * 2^a * 2^g
local notation "kind" => (fun k : Fin (2^a₀) => NewSlots.kindOf (Equiv.symm (refreshSlots hd) k))
local notation "pub" => (fun k : Fin (2^a₀) => AllSlots.words (2^a) (2^g) I T (Equiv.symm (refreshSlots hd) k))

/-- All actual slot passes and the base-output pass, in their execution order. Both levels
of incidence and all actual widths are available by direct addressing in the final memory. -/
theorem incidence_output (src : AllSlots.SourceTables X E hdH conn F choice I mem)
    (fit : AllSlots.Fits (a₀ := a₀) X bits) (layout : T.Layout Y)
    (apart : AllSlots.InputsApart T kind pub N) :
    let M := (template BaseOutput.visit 0).instantiate bits (BaseOutput.params T a₀ g)
    ∃ slotReports baseReports,
      let m₁ := after mem (eventLog slotReports)
      let m₂ := after m₁ (eventLog baseReports)
      AllSlots.Runs kind pub N (List.finRange (2^a₀)) mem slotReports ∧
      runSegment M.program 29 (some 0) m₁ (List.replicate (BaseOutput.baseCount Y) []) = some baseReports ∧
      T.Represents Y m₂ ∧
      (∀ addr, AllSlots.Outside T (N * 2^a₀) addr → BaseOutput.Outside T Y addr → m₂ addr = mem addr) ∧
      RAMBuckets.cost Report.probes (slotReports ++ baseReports) =
        (6 + 7*dH + 4*(2^a₀-(dH+1))) * X.positions + 5 * BaseOutput.baseCount Y := by
  obtain ⟨s,hs,actual,fs,cs⟩ := AllSlots.all_slots X E hdH conn F hD hd choice I T mem src fit layout apart
  obtain ⟨b,hb,rep,fb,cb,_,_⟩ := BaseOutput.base_pass T Y (after mem (eventLog s)) layout actual
  refine ⟨s,b,hs,hb,rep,fun addr ho ht => (fb addr ht).trans (fs addr ho), ?_⟩
  exact (RAMBuckets.cost_append Report.probes s b).trans (congrArg₂ (· + ·) cs cb)

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
