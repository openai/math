import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentDatedRangeRegisters
import OAI.Hierarchy.DescentReachedLocalNodes

namespace OAI
/-! # Retained operand registers on prefixes of a selected dated history -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentRetainedRangeDigits
open Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k wire hist w : ℕ}

variable {W₀ W : MarkedWorld F d P bits} {i₀ z₀ D₀ j z D : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {now : Reached W G q ε S k j z D wire hist}
    {p : ℕ} (hp : 0<p) (a : Archive W₀) (number : Local a.bit) (path : Path start now)
    (ports : ℕ→DatePorts) (memory : ℕ→Memory w)
    (room : ∀{U : MarkedWorld F d P bits} {i g C : ℕ} {r : Reached U G q ε S k i g C wire hist},
      ∀(prefix_ : Path start r) (whole : prefix_.whole p),
        (∃suffix_ : Path r now,prefix_.append suffix_=path) →
          RangeRoom (ports i) r (prefix_.archive p hp a whole).bit)

/-- A selected prefix uses the original archive order and the RAM returned at its own date.
A register on a path outside the selected history is never queried by the date induction. -/
def registeredPages {U : MarkedWorld F d P bits} {i g C : ℕ} {r : Reached U G q ε S k i g C wire hist}
    (prefix_ : Path start r) (whole : prefix_.whole p) : Register (prefix_.archive p hp a whole).bit :=
  if onPath : ∃suffix_ : Path r now,prefix_.append suffix_=path then
    let ok:=room prefix_ whole onPath
    rangeRegister (ports i) r (prefix_.archive p hp a whole).bit
      (trajectory p hp a number prefix_ whole) ok.capacity ok.hosts ok.groups ok.radix ok.positive (memory i)
  else {field:=0,nodes:=1,number:=fun _=>0,packed:=fun _ _ _=>0}

theorem registeredPages_at {U : MarkedWorld F d P bits} {i g C : ℕ} {r : Reached U G q ε S k i g C wire hist}
    (prefix_ : Path start r) (suffix_ : Path r now) (cut : prefix_.append suffix_=path) (whole : prefix_.whole p) :
    let ok:=room prefix_ whole ⟨suffix_,cut⟩
    registeredPages hp a number path ports memory room prefix_ whole =
      rangeRegister (ports i) r (prefix_.archive p hp a whole).bit
        (trajectory p hp a number prefix_ whole) ok.capacity ok.hosts ok.groups ok.radix ok.positive (memory i) :=by
  dsimp only
  unfold registeredPages
  rw [dite_eq_left (show ∃s : Path r now,prefix_.append s=path from ⟨suffix_,cut⟩)]

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
