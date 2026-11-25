import OAI.Hierarchy.GridReceiverBankAddresses
import OAI.Hierarchy.GridReceiverDirectory
import OAI.Hierarchy.TraceReceiverScheduledSource

namespace OAI
/-! # The addresses used by the selected-root map and the weighted receiver -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridReceiverBanks

open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open NavigationPass NavigationDirectory TraceDistribution TraceAdmission GridRegisteredSetting

variable {F : Type} [Field F] [Fintype F] {w pc regs words size baseAddr fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs words size baseAddr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "d" => GridReceiverDirectory.native D l
local notation "a" => (d).archive
local notation "W" => (64*w)
local notation "s" => TickWorkspace.base (receiverAge w)
local notation "x" => (a).terminal (d).stages (d).edges W

/-- The histogram prefix consumes a public number of bits on every valid
history. The first shared bit can therefore be an immediate of the ROM. -/
def arena : TickTerminalRoot.Arena where
  control := s 18
  selected := s 17
  rootHeader := (tasks w).first
  results := s 13
  wireStart := (a).oldHistory+W*(a).histWords (d).stages
  wirePrefix := (x).prefixBase
  physicalPins := l.pinWidth
  metadata := s 9
  seed := s 14
  map := s 14+64
  commands := s 15
  arguments := s 16

/-- Owner-class and local bit-interval prefix scans in T use the same public
key layout, with D and its registered costs recomputed in T's own memory. -/
def pinPlan : GridPinPublisher.Plan :=
  GridPinPublisher.canonical w (l.dimension+1) l.sideMinusOne l.copies l.pinWidth
    (GridNativeImage.parameterCount D l) (l.selectorCap+1) l.receiverText l.bank
    (GridControllerSimGeometry.railCount l.dimension l.sideMinusOne l.bank)
    size (d).parameters.roots (d).stages.length (2^(axes+1)) (2*2^(w/2))

/-- Full native trace and record-table input. Offset words include T's two
initial scalar literals, as witnessed by the genuine header shift. -/
theorem suffix_address (enough : D.block.repeatFactor*
    ((D.block.cursorState D.axesFit (w/2) (1+((axes+1+w/2)+(axes+1+w/2)))
      (TraceStaticRow.gateTable D.field D.fit.width D.fit.labels baseAddr fuel D.state regs words
        (axes+1+w/2)).cells).maxWidth+1)*D.block.widthBase^D.passes<2^W)
    (h : D.run.plan.History) :
    let depth:=axes+1+w/2
    let G:=TraceStaticRow.gateTable D.field D.fit.width D.fit.labels baseAddr fuel D.state regs words depth
    let tab:=physicalTable D.block D.axesFit (w/2) (1+(depth+depth)) G.cells D.passes W D.passesFit enough
    (arena D l).wireStart=(a).phase+1+(D.run.plan.write tab.codes h).length := by
  intro depth G tab
  have sized:=(physical_record_codec D.block D.axesFit (w/2) (1+(depth+depth)) G.cells
    D.passes W D.passesFit enough h).1
  rw [sized]
  change (a).phase+1+W*(D.block.alphabetCap*(stageCounts D.block D.passes (axes+1)).sum)=_
  ac_rfl

theorem shape_fields : (arena D l).physicalPins=l.pinWidth ∧ (arena D l).selected=(tasks w).selected ∧
    (arena D l).results=(tasks w).results ∧ (arena D l).rootHeader=(tasks w).first ∧
    (arena D l).wirePrefix=(x).prefixBase := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Hierarchy.GridReceiverBanks
end

end OAI
