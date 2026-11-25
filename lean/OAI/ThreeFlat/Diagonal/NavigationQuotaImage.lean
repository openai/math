import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.NavigationDirectory

namespace OAI
/-! # The dense selector rows retained after a native stage -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM NavigationDirectory
noncomputable section

/-- The accepted branch owns the exact packed row which survived the native stage. -/
def QuotaImage {W K n:ℕ} (Q : PhysicalStage.RecordFamily n) (fit : Q.Fits K W)
    (branch : Fin n) (c : Cursor) (out : Memory W) : Prop :=
  c.dense+K*Q.motifs≤c.heap ∧ ∀ (i:Fin Q.motifs) (j:Fin K),
    out (c.dense+K*i.val+j.val)=HistogramRegister.words (Q.rows fit) (Q.sequence fit branch) i j

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
