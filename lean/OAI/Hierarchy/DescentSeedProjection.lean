import OAI.Hierarchy.DescentEpochHistory
import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! # The original public histogram and its true field weight on every surviving transcript -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
noncomputable section
universe v
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} (G : PoweredGadget F) {u ε : ℝ} (hu : 0≤u) (he : 0≤ε)

namespace Schedule
def seedChoice : {t : ℕ}→{H : Histories.{0, 0, v} F d P bits}→
    (run : Schedule G (u:=u) he t H)→(finish G he run).Choice→H.Choice
  | 0,_,_,c=>c
  | t+1,_,run,c=>(@seedChoice t _ run.2 c).1

theorem weight_initial {t : ℕ} (H : Histories F d P bits) (run : Schedule G (u:=u) he t H)
    (c : (finish G he run).Choice) : (finish G he run).weight c=H.weight (seedChoice G he run c) := by
  induction t generalizing H with
  | zero=>rfl
  | succ t ih=>exact ih _ run.2 c
end Schedule

namespace Epochs
variable {t h C Ht : ℕ}
def seedChoice : {J : ℕ}→{H : Histories.{0, 0, v} F d P bits}→
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)→(finish G hu he run).Choice→H.Choice
  | 0,_,_,c=>c
  | j+1,_,run,c=>Schedule.seedChoice G he run.1.subrounds (@seedChoice j (run.1.finish G hu he) run.2 c)

theorem weight_initial {J : ℕ} (H : Histories F d P bits)
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (c : (finish G hu he run).Choice) :
    (finish G hu he run).weight c=H.weight (seedChoice G hu he run c) := by
  induction J generalizing H with
  | zero=>rfl
  | succ j ih=>
    let next := seedChoice G hu he run.2 c
    exact (ih (run.1.finish G hu he) run.2 c).trans
      (Schedule.weight_initial G he H run.1.subrounds next)

end Epochs
end
end Hierarchy.DescentSixParty

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing Catalyst DescentSixParty
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s : ℕ)
variable {u ε : ℝ} (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε) {J h C Ht t : ℕ}
local notation "H" => initialGroup X R s
local notation "start" => Histories.seedInternal (markedInput X) s (Sum.elim (fun _=>true) (fun _=>false))

theorem weight_seed_product (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (c : (Epochs.finish G hu he run).Choice) :
    (Epochs.finish G hu he run).weight c=∏j : Fin R,(start).weight (Epochs.seedChoice G hu he run c j) :=
  Epochs.weight_initial G hu he H run c

end
end Hierarchy.DescentInitialHost

end OAI
