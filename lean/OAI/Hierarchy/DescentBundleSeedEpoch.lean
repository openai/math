import OAI.Hierarchy.DescentOriginalRetainedSeed
import OAI.Hierarchy.DescentBundleEpoch
import OAI.Hierarchy.DescentBundleSeed
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # Complete bundled local coefficients starting at the actual census and equality hubs -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentKernelHistory DescentSixParty DescentInitialHost Catalyst DescentRotor DescentCompiler
open LinearAlgebra.SpectralBooks ThreeFlat Expander NonlinearExpanders
noncomputable section
variable {F : Type} [Field F] {k n p R : ℕ} (X : Approximation F k n) (count s : ℕ)
variable (hp : 0<p) (one : 1≤R) (multiple : p∣s)

theorem grainAt_multiple (S : AtomSchedule) (b age : ℕ) : p∣S.grainAt b p age :=
  dvd_mul_right p _

variable {G : PoweredGadget F} {u ε : ℝ} {hu : 0≤u} {he : 0≤ε} {t h C Ht nB J : ℕ}
variable {board : Graph nB h} {bitsR : ℕ} (menu : ∀π,Configures F board.arcs C bitsR π)
variable (wide : max 1 (max bitsR (C*bitsR))≤R)

def seedEpochs (S : AtomSchedule)
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X count s))
    (issued : Epochs.Grains board bitsR (fun e i=>S.grainAt G.b p (e*(S.rounds+1)+i)) 0 run)
    (c : (Epochs.finish G hu he run).Choice) : Retained p R ((Epochs.finish G hu he run).state c) :=
  epochs hp one (fun _=>by simpa using multiple) menu wide run _ 0 issued
    (fun _ _ _=>grainAt_multiple S _ _) (seedRetained X count s hp one multiple) c

end
end Hierarchy.DescentBundleHistory

end OAI
