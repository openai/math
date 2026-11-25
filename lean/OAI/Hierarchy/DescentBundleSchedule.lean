import OAI.Hierarchy.DescentBundleWorld
import OAI.Hierarchy.DescentScheduledBitHistory
import OAI.Hierarchy.DescentScheduleGrains

namespace OAI
/-! # Whole physical operands throughout the chosen measured ordinary subround tree -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty Computability.BorderVNP.Crossing
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {u ε : ℝ} {G : PoweredGadget F} (he : 0≤ε) {B : BitDescription W}
variable (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)

def WorldShape.scanned (T : StageInput W G u ε) (s : WorldShape p R B)
    (unit : p∣T.z) (c : (T.result he).Choice) : WorldShape p R (BitDescription.scanned he T B c) :=
  let rows:=BitDescription.scannedRows he T
  (s.selected hp one pins G rows.pick (fun _=>T.z) (fun _=>T.unitPos) rows.fit
    (fun _=>le_refl T.z) rows.pack (rows.profile c) (fun _=>unit)).transport (rows.state c).symm

def WorldShape.extend {H : Histories F d P bits} (stage : SubroundInput H G (u:=u) he)
    {old : ∀c,BitDescription (H.state c)} (s : ∀c,WorldShape p R (old c))
    (z : ℕ) (issued : SubroundInput.Grain z stage) (unit : p∣z) (c : (H.extend he stage).Choice) :
    WorldShape p R (BitDescription.extend he H stage old c) := by
  have pos : 0<z := (issued.1 c.1) ▸ (stage.placement c.1).unitPos
  exact WorldShape.follow hp pos unit _ (issued.2 c.1 c.2)
    (WorldShape.scanned he hp one pins (stage.placement c.1) (s c.1) ((issued.1 c.1).symm ▸ unit) c.2)

def WorldShape.schedule {t : ℕ} {H : Histories F d P bits} (plan : Schedule G (u:=u) he t H)
    (z : ℕ→ℕ) (issued : Schedule.Grains z plan) (unit : ∀i<t,p∣z i)
    {old : ∀c,BitDescription (H.state c)} (s : ∀c,WorldShape p R (old c))
    (c : (Schedule.finish G he plan).Choice) : WorldShape p R (BitDescription.schedule he plan old c) := by
  induction t generalizing H z with
  | zero=>exact s c
  | succ t ih=>
    rcases plan with ⟨stage,rest⟩
    exact ih rest (fun i=>z (i+1)) issued.2 (fun i h=>unit (i+1) (by omega))
      (WorldShape.extend he hp one pins stage s (z 0) issued.1 (unit 0 (by omega))) c
end
end Hierarchy.DescentBundleHistory

end OAI
