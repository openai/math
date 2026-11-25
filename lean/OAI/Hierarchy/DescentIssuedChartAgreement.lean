import OAI.Hierarchy.DescentActorDestination
import OAI.Hierarchy.DescentHubCoalescence

namespace OAI
/-! The numeric venue and donor halo depend only on measured colony coordinates
and the original hub flag of a resident. -/
namespace Hierarchy.DescentStageEdgeReceipt.IssuedDonorChart
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentHostDirectory
open scoped Classical
noncomputable section
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits:P→ℕ}
    {W:MarkedWorld F d P bits} {G:PoweredGadget F} {u ε:ℝ}
    (he:0≤ε) (T:StageInput W G u ε) (c:(T.result he).Choice)
    (a b:IssuedDonorChart he T H)
local notation "S" => scanWorld he T c

theorem same_col : a.col=b.col := eq_of_heq (a.native.trans b.native.symm)

theorem same_key : a.key he T c=b.key he T c := by
  exact congrArg (fun col => StarKeys.nativeKey W.graph W.core
    (scanHomeAt he T) (scanColorAt he T) T.cap col a.same
    (bestLayout (branchWidth G (fun _ : (BitDescription.scannedRows he T).pairs => T.z)
      ((BitDescription.scannedRows he T).profile c)))) (same_col he T a b)

theorem same_hub (v:(S).graph.Site) : a.hub ((a.key he T c) v).1=b.hub ((b.key he T c) v).1 := by
  obtain ⟨x,loc⟩:=a.key_host he T c v
  have active : ((b.key he T c) v).1=(b.col (scanHomeAt he T x)).1 := by
    simpa only [same_key he T c a b,same_col he T a b] using loc
  rw [loc,active,(a.old x).2,(b.old x).2]

theorem same_address (k g:ℕ) (v:(S).graph.Site) :
    (MarkedWorld.address S (a.key he T c) a.hub k g v).val=
    (MarkedWorld.address S (b.key he T c) b.hub k g v).val := by
  change mergeHub a.hub k g _=mergeHub b.hub k g _
  unfold mergeHub
  rw [same_hub he T c a b v,same_key he T c a b]

theorem same_reclaimed (k g:ℕ) :
    MarkedWorld.reclaimed S (a.key he T c) a.hub k g=
      MarkedWorld.reclaimed S (b.key he T c) b.hub k g := by
  unfold MarkedWorld.reclaimed
  apply congrArg (fun f:(S).graph.Site→_=>Finset.univ.image f)
  funext v
  exact same_address he T c a b k g v

theorem native_key (c₀:IssuedDonorChart he T T.V)
    (same:∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e)) :
    c₀.key he T c=DescentSixParty.StarKeys.nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T)
      T.cap (nativeAddress he T) same
      (DescentSixParty.bestLayout (branchWidth G (fun _: (BitDescription.scannedRows he T).pairs=>T.z)
        ((BitDescription.scannedRows he T).profile c))) :=by
  have eqn:c₀.col=nativeAddress he T:=eq_of_heq c₀.native
  exact congrArg (fun col => StarKeys.nativeKey W.graph W.core
    (scanHomeAt he T) (scanColorAt he T) T.cap col same
    (bestLayout (branchWidth G (fun _ : (BitDescription.scannedRows he T).pairs => T.z)
      ((BitDescription.scannedRows he T).profile c)))) eqn

end
end Hierarchy.DescentStageEdgeReceipt.IssuedDonorChart

end OAI
