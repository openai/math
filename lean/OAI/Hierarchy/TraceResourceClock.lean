import OAI.Hierarchy.TraceResourcePipeline
import OAI.Hierarchy.TraceRecordScale

namespace OAI
/-! # Charging the complete native resource registration at the grid scale -/
namespace Hierarchy.TraceAdmission.Resources
open TraceDistribution Filter

/-- The actual native timing includes both setup headers, every parent walk,
every linked-list insertion, both resource-table passes and the public row copy. -/
def registrationTicks (pc rc stages : ℕ) (p : Parameters ℕ) :=
  67+((11+(stages+1)*p.lanes*(2*(Parents.row pc).work+4)+(9+4*p.roots+10*p.lanes))+
    (ticks rc p+(6+5*resourceLength p)))

def coefficient :=
  120+2*(Parents.row 0).work+
    2*max (scratchExpr (fields 0)).work (resourceExpr (fields 0)).work

theorem registrationTicks_bound (pc rc stages : ℕ) (p : Parameters ℕ) :
    registrationTicks pc rc stages p ≤
      coefficient*(1+(stages+1)*p.lanes+(p.lanes+1+p.roots)*(p.directions+2)) := by
  let X := (stages+1)*p.lanes
  let Y := (p.lanes+1+p.roots)*(p.directions+2)
  let S := max (scratchExpr (fields 0)).work (resourceExpr (fields 0)).work
  let P := (Parents.row 0).work
  have same : (Parents.row pc).work=P := rfl
  have unchanged : max (scratchExpr (fields rc)).work (resourceExpr (fields rc)).work=S := rfl
  have table : ticks rc p ≤ 22+Y*(2*S+4) := by
    simpa only [Y,unchanged] using ticks_bound rc p
  have root : p.roots≤Y := (show p.roots≤p.lanes+1+p.roots by omega).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have lanes : p.lanes≤Y := (show p.lanes≤p.lanes+1+p.roots by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  have row : resourceLength p≤Y := Nat.mul_le_mul_right _ (by omega)
  unfold registrationTicks
  rw [same]
  change 67+((11+X*(2*P+4)+(9+4*p.roots+10*p.lanes))+(ticks rc p+(6+5*resourceLength p)))≤
    (120+2*P+2*S)*(1+X+Y)
  calc
    _ ≤ 67+((11+X*(2*P+4)+(9+4*Y+10*Y))+(22+Y*(2*S+4)+(6+5*Y))) := by gcongr
    _ ≤ _ := by ring_nf;omega

theorem eventual_registration_time {u s : ℕ→ℕ} (scale : Scale u s) (A : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ (p : Parameters ℕ) (stages pc rc : ℕ),
      let axes:=u w+1-w/2
      p.roots≤axes*2^axes → p.lanes≤2^axes → p.directions≤w → stages≤A*(s w+1) →
      registrationTicks pc rc stages p≤2^(3*w/5) := by
  filter_upwards [descriptor_room scale (max A coefficient)] with w budget
  intro p stages pc rc axes hr hl hd hs
  exact (registrationTicks_bound pc rc stages p).trans <|
    (Nat.mul_le_mul_right _ (le_max_right A coefficient)).trans
      (budget p.roots p.lanes p.directions stages hr hl hd
        (hs.trans (Nat.mul_le_mul_right _ (le_max_left A coefficient))))

end Hierarchy.TraceAdmission.Resources

end OAI
