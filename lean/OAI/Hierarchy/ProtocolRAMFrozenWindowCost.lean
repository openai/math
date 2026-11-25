import OAI.Hierarchy.ProtocolRAMFrozenFormat
import OAI.Hierarchy.ProtocolRAMPackedCost

namespace OAI
/-! # Native instruction counts for the complete reserved-format publisher -/
namespace Hierarchy.ProtocolRAMFrozenWindow
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM TaggedShorterReportedPublish

theorem Format.cheap (f : Format) (W r : ℕ) (a : Inputs) : CheapCode (f.phase W r a) := by
  have anchors : CheapCode (f.anchorPhase W r a) :=
    cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)) (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _))
  let s := f.window
  let A := f.tables r a
  have rank : CheapCode (f.rankPhase W r a) :=
    ProtocolRAMPackedRanked.cheap (s.rank r) W f.N s.bins a.width
      (s.anchor r 2) a.bias a.classes a.weights
  intro P R K pc reg pub exit i
  exact cheap_seq anchors (cheap_seq rank
    (cheap_seq (clearedProcedure_cheap W (s.base r) s.maskWords (s.src r) (f.N*f.cap) f.γ r A)
      (TaggedShorterSlotWidth.cheap W (s.widthBase r) f.groups f.D (s.widthSrc r)
        (f.N*f.cap) f.γ (r+1) A a.origins))) pc reg pub exit i

theorem Format.clock_eq (f : Format) (r : ℕ) (a : Inputs) :
    f.clock r a=121+f.N*(8*a.owner.work+479)+6*f.window.bins+
      6*f.window.maskWords+6*f.window.widthWords+20360*(f.N*f.cap) := by
  simp only [Format.clock,ProtocolRAMSupergroupPorts.work,ProtocolRAMPackedRanked.clock_eq]
  ring

end Hierarchy.ProtocolRAMFrozenWindow

end OAI
