import OAI.Computability.BorderVNP.DiagonalNativeCanonicalBoot

/-! # Rejection of every positive signed path on an invalid encoded profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator PackedHistoryCircuit BorderVNP.Cube BorderVNP.Cube.Tally

/-- On a completed positive header, failure of the actual geometry profile forces the
positive native value to vanish for every time and burst cutoff. This covers exterior
assignments for which there is no authenticated source layout to charge. -/
theorem positiveMasked_zero_of_profile_empty {dim box lanes selectors symbols R r t d link inner n w : ℕ} {Edge : Type}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (G : Wiring R r t d link inner n Edge)
    (mac : TeamOpcode.Macros w 8) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (u : Fin (R+1)) (ticks burst clock : ℕ) (trace : List (TeamRAM.Event w)) (z : Bank w) (saved : Memory w) :
    let ad := args u
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let f := G.transferFrame u ad.header ad.dst
    let initial := processorMemory F w
    Runs (pub u) mac JointHeader.bootHeader (reg u) initial trace z saved →
    f.Stable (readings z) → (saved f.dst).val ≠ 0 →
    ¬ Nonempty (Returns (withStartup pinGeometry) (pub u) mac (reg u) initial) →
    positiveMaskedNativeValue G (signedBody id) mac pub reg args pin ticks burst clock ext u = 0 := by
  intro ad F f initial boot stable positive empty
  by_cases zero : modeTag (w := w) G args pin ext u = 0
  · exact ite_eq_left zero
  rw [positiveMaskedNativeValue,ite_eq_right zero]
  let machine := processorMachine (signedProgram id) (pub u) mac (reg u) F
  have impossible : IsEmpty (NativePath machine ticks burst clock) := by
    constructor
    intro p
    obtain ⟨⟨v,mv,run⟩,_⟩ := (signedProgram_execute_iff id).mp p.property.1
    obtain ⟨history,_,_,_⟩ := (evaluation_geometry_iff f PrivatePlacement.program
      (scheduleGroups dim (selectorWidth dim selectors lanes))
      (signedInputs id (TeamRows.ownedGroups dim box lanes selectors symbols)) signedOccurrences boot stable positive).mp run
    exact empty ⟨history⟩
  change nativeValue machine ticks burst clock = 0
  simp [nativeValue]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
