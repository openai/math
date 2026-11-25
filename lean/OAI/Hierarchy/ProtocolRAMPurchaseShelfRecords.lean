import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseSignedDispatch

namespace OAI
/-! # Candidate trajectories, decisions and physical flag decoding -/
namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ}
theorem decode_flag (width : 0<w) (b : Bool) : decide (MarkTape.encode w b≠0)=b := by
  have neq : (1:Word w)≠0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow width.ne'),Fin.val_zero] at hv
    omega
  cases b <;> simp [MarkTape.encode,neq]
end
end Hierarchy.ProtocolRAM.PurchaseStage

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
open PurchaseCT AdaptiveProbe
noncomputable section
variable {z d k : ℕ}
def marked (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (mem : Mem z d) (i : Key z d k) :=
  PurchaseMarks.stratum (n:=2^z) phase T kind sh.table (sh.stock (stage i)) mem (axis i)

def decisions (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (mem : Mem z d) (i : Key z d k) :=
  let t := stage i
  let tiles := advisedStage z d π t
  let ps := PurchaseTape.paths tiles (Fintype.equivFin (stageAt z d t).Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows _)) depth
  MarkTape.decisions ps ((sh.marked phase T kind mem i).map Fin.castSuccEmb)

@[simp] theorem decisions_len (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (mem : Mem z d) (i : Key z d k) :
    (sh.decisions S π depth phase T kind mem i).length=paths z S.degree depth := by
  simp [decisions,PurchaseTape.paths,paths]

theorem decisions_count (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (mem : Mem z d) (i : Key z d k) :
    (sh.decisions S π depth phase T kind mem i).count true=
      (advisedPurchases S π (stage i) depth (sh.marked phase T kind mem i)).1.length := by
  simp only [decisions,MarkTape.decisions_count,PurchaseTape.paths,PurchaseDFS.scan_filled,List.length_map,advisedPurchases]

abbrev pathRows (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (i : Key z d k) :=
  let t:=stage i
  PurchaseStage.liveRows (advisedStage z d π t) (Fintype.equivFin (stageAt z d t).Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows _)) depth
end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open scoped Classical
noncomputable section

open PurchaseFrozen in
def actualMarks {z d k : ℕ} (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen : Shelf.Mem z d) (s : StageAt z d) (c : Fin k × Bool) :=
  sh.marked phase T kind frozen (key s ((PurchaseMarks.signedDirection k).symm c))
end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
