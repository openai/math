import OAI.Computability.BorderVNP.RoutingISAScheduleClockTotal

/-! # Quantitative phase boundaries of the signed team execution

The private call budget is paired with the argument directory producing
those calls. The packet lookup following the calls has a separate bound
from the owned-group scan that generated its vertex count. This separation
works also when the individual maxima occur on different signed paths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

/-- Length-only charges at the five boundaries of the signed evaluation
branch. The core covers the physical startup, branch, pins and routed data. -/
structure PhaseCharges where
  /-- Startup, pins, branch and route work combined. -/
  core : ℕ
  /-- Public geometry, demand directories and the grouping schedule. -/
  before : ℕ
  /-- Owned cube work, cell arguments, and the private call probes. -/
  argumentsCalls : ℕ
  /-- Post-call packet IDs and aligned tally work. -/
  finish : ℕ
  /-- Staged final matrix entry, including the lead-team test. -/
  reader : ℕ

/-- The initial placement and populated demand directory before routing. -/
def beforeDirectory (R V entries : ℕ) := PrivatePlacement.setup.slots+entries*15+1+
  (Packing.Directory.ISA.setup.slots+(Packing.Directory.ISA.candidate.slots+19)*(8*(R*V))+8)

/-- The six-word bundle, cell-control and typed-task directories after routing. -/
def argumentDirectory (cells bundles : ℕ) := Packing.BundleDirectory.setup.slots+16*cells+30*bundles+1+
  (CellControlRows.setup.slots+cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots+
    (TypedTaskBuilder.setup.slots+cells*(TypedTaskBuilder.body.slots+1)+2))

/-- The measured outer work of cell reports, supplemental placement, typed
packet staging and all private argument probes. -/
def cellWork (w publicWords powerSlots exterior : ℕ) :=
  5000*((w+1)*publicWords)+700000000*((w+1)*exterior)+500*powerSlots

/-- Split the finite allowances at the semantic cut points. Each of the
two independent cube windows can use its full fixed-format coefficient. -/
def phaseCharges (core geometry fixed R V entries cells bundles desc decl cables cubeUnits
    F H w publicWords powerSlots exterior rectangle reader : ℕ) : PhaseCharges :=
  ⟨core,geometry+beforeDirectory R V entries+desc+decl,
    fixed+argumentDirectory cells bundles+32*desc+(82*cables+F*cubeUnits)+cellWork w publicWords powerSlots exterior,
    F*cubeUnits+64*(publicWords+powerSlots+H*cubeUnits)+rectangle,reader⟩

/-- All windows fit the computed total bound, independently of which genuine
signed path attains each individual window. The factor two accounts for
charging both the pre-call cube loops and the later ID-emission window. -/
theorem sum_le_completeAllowance (core geometry fixed R V entries cells bundles desc decl cables cubeUnits
    F H w publicWords powerSlots exterior rectangle reader : ℕ) :
    let c := phaseCharges core geometry fixed R V entries cells bundles desc decl cables cubeUnits F H w
      publicWords powerSlots exterior rectangle reader
    c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤
      completeAllowance core geometry fixed R V entries cells bundles desc decl cables cubeUnits (2*F) H w
        publicWords powerSlots exterior (rectangle+reader) := by
  dsimp [phaseCharges,completeAllowance,beforeDirectory,argumentDirectory,directoryWork,cellWork]
  exact le_of_eq (by ring)

/-- Once the group traversal has produced its real vertex count, the separate
ID and suffix budget fits the fixed-format local window regardless of the
number of public cable rows. -/
theorem packetID_window (n b h K s width vertices units : ℕ) (nonempty : 1 ≤ units)
    (visited : vertices ≤ BorderVNP.Cube.TeamRowClock.physicalCoefficient n b h K s * units) :
    packetIDTicks vertices width ≤ cubeCoefficient n b h K s width*units := by
  rw [packetIDTicks_eq]
  unfold cubeCoefficient
  have cost := Nat.mul_le_mul_left (43+33*width) visited
  have one := Nat.mul_le_mul_left 109 nonempty
  rw [mul_one] at one
  calc
    _ ≤ 109*units+(43+33*width)*(BorderVNP.Cube.TeamRowClock.physicalCoefficient n b h K s*units) :=
      Nat.add_le_add one cost
    _ ≤ _ := by ring_nf; omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
