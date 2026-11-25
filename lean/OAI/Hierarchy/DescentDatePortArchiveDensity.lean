import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The two actual incoming pitches on the chronological ports -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentDatedSeedStartup
open DescentInitialHost DescentSIMDLookup
noncomputable section

/-- Every complete incoming row pays its word by its lanes.  A cropped bus may
hold the complete group range, in which case the old host pays one word. -/
structure ArchiveDensity (ports : DatePorts) (groups h argUnit roleUnit : ℕ) : Prop where
  operands : groups≤ports.operandLanes ∨ h≤ports.operandLanes*argUnit
  roles : groups≤ports.roleLanes ∨ h≤ports.roleLanes*roleUnit

theorem ArchiveDensity.weaken {p : DatePorts} {G h a b c d : ℕ} (old : p.ArchiveDensity G h a b)
    (args : a≤c) (role : b≤d) : p.ArchiveDensity G h c d :=
  ⟨old.operands.imp_right (fun z=>z.trans (Nat.mul_le_mul_left _ args)),
    old.roles.imp_right (fun z=>z.trans (Nat.mul_le_mul_left _ role))⟩

/-- Both original seed registers are words from the actual selected initializer. -/
theorem initial_density {F : Type} [Field F] {cp n : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F cp n) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups h Z a b : ℕ)
    (args : h≤l.operandLanes*a) (role : h≤(Primitive.paletteLanes G op l.seedWidth Z h k)*b) :
    (initial G op X R l k H groups h Z).ArchiveDensity groups h a b :=⟨.inr args,.inr role⟩

/-- The operand word and the global primitive word can use different physical pitches. -/
theorem ordinary_density {F P : Type} [Field F] (v : PhysicalOrdinary F P) (base groups h a b : ℕ)
    (words : h≤v.resolver.lanes*a) (global : h≤v.palette.nextLanes*b) :
    (ordinary v base).ArchiveDensity groups h a b :=⟨.inr words,.inr global⟩

/-- The last descendant of the actual reset writes both lasting pages at the
chosen receiver cut. This includes the case of a single short group row. -/
theorem reset_density {w : ℕ} (v : PhysicalReset) (base : ℕ) (u : v.DateInputs base w) (groups h C : ℕ)
    (density : groups≤v.successor.receiver.lanes ∨ h≤v.successor.receiver.lanes*C)
    (same : v.successor.primitive.chart.lanes=v.successor.receiver.lanes) :
    (reset v base u).ArchiveDensity groups h C C :=by
  refine ⟨density,?_⟩
  change groups≤v.successor.primitive.chart.lanes ∨ h≤v.successor.primitive.chart.lanes*C
  rwa [same]

theorem reset_packet_density {G M blocks h u : ℕ} (density : G≤M ∨ h≤M*u) :
    G*blocks≤M*blocks ∨ h≤M*u:=density.imp_left (fun g=>Nat.mul_le_mul_right blocks g)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
