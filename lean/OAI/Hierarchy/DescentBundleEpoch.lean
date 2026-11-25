import OAI.Hierarchy.DescentOriginalRetainedWorld
import OAI.Hierarchy.DescentBundleSchedule
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentEpochGrains

namespace OAI
/-! # Complete retained p-wide histories through every ordinary and installed reset epoch -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat Expander NonlinearExpanders
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {H : Histories F d P bits}
variable {u ε : ℝ} {G : PoweredGadget F} {hu : 0≤u} {he : 0≤ε} {t h C Ht n : ℕ}

variable (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)
variable {board : Graph n h} {bitsR : ℕ} (menu : ∀π,Configures F board.arcs C bitsR π)
variable (wide : max 1 (max bitsR (C*bitsR))≤R)

def epoch (E : Epoch H G hu he t h C Ht) (z : ℕ→ℕ) (issued : Epoch.Grains z board bitsR E)
    (calendar : ∀i≤t,p∣z i) (old : ∀c,Retained p R (H.state c))
    (c : (E.finish G hu he).Choice) : Retained p R ((E.finish G hu he).state c) := by
  let mid := BitDescription.schedule he E.subrounds (fun v=>(old v).description) c
  have s : WorldShape p R mid := WorldShape.schedule he hp one pins E.subrounds z issued.ordinary
    (fun i hi=>calendar i hi.le) (fun v=>(old v).shape) c
  have all : p∣E.grain := issued.grain ▸ dvd_mul_of_dvd_left (calendar t (le_refl t)) G.b
  let split := BitDescription.granular _ (E.count c) E.grain (E.fit c) mid
  have sg : WorldShape p R split := s.granular (E.count c) E.grain (E.fit c) hp E.positive all
  let key := DescentOrderedReset.grains _ (E.count c) (E.order c)
  let Z := E.reset c
  let T := E.terminals c
  have zu : p∣Z.unit := (issued.unit c).symm ▸ all
  have positive : 0<Z.unit := (issued.unit c).symm ▸ E.positive
  have fit : Z.unit=(Z.unit/p)*p := (Nat.div_mul_cancel zu).symm
  let cfg := issued.menu menu c
  let bank := split.batchedReset Z T key (Z.unit/p) p hp fit cfg
  have sb : WorldShape p R bank := reentryWorldShape sg Z T key _ hp fit cfg one (by
    change max 1 (max (E.reset c).width (C*(E.reset c).width))≤R
    rwa [issued.width c])
  exact ⟨BitDescription.follow (E.reblock c) bank,WorldShape.follow hp positive zu _ (issued.cuts c) sb⟩

def epochs {J : ℕ} (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (period : ℕ→ℕ→ℕ) (j : ℕ) (issued : Epochs.Grains board bitsR period j run)
    (calendar : ∀e i,i≤t→p∣period e i) (old : ∀c,Retained p R (H.state c))
    (c : (Epochs.finish G hu he run).Choice) : Retained p R ((Epochs.finish G hu he run).state c) := by
  induction J generalizing H j with
  | zero=>exact old c
  | succ J ih=>
    rcases run with ⟨E,rest⟩
    exact ih rest (j+1) issued.2 (epoch hp one pins menu wide E (period j) issued.1 (calendar j) old) c

end
end Hierarchy.DescentBundleHistory

end OAI
