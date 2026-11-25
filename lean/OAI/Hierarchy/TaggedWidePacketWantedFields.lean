import OAI.Hierarchy.ProbeSignedWantedRelease
import OAI.Hierarchy.TaggedWidePacketMenuControls

namespace OAI
/-! # Native pre-release widths for the elected atom of the original fixed packet menu -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open ThreeFlat.RAM.DescriptorExpr
open AdaptiveProbe Probe WireTelescope ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {F E A : Type} [Field F] [Fintype E] [Nonempty E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ} {N S W : ℕ}
variable (M : FixedMenu F edge req box ε tree N) (copies : ℕ) (party : Fin k→Expr)

/-- Archived numeric packet tag dispatches over the *original* finite positive
requests. Repeated local requests remain repeated in the physical release. -/
def wantFor (chosen : M.index) (here width nbr : Expr) : Expr :=
  .branch .eq width (.lit 0) (.lit 0)
    (lowBefore (fun a : PositiveDemand req chosen.val.val=>edge (req a.val)) party .row here nbr
      (.lit (copies*(M.packet chosen).width)))

def wantField (tag here width nbr : Expr) : Expr :=
  chooseField (Fintype.card M.index) 1
    (fun i=>wantFor M copies party ((Fintype.equivFin _).symm i) here width nbr) tag

theorem want_at (m : Memory W) (row : Word W) (tag here width nbr : Expr) (choice : M.index)
    (fits : 1+Fintype.card M.index≤2^W)
    (authenticated : (tag.eval m row).val=(Fintype.equivFin _ choice).val+1) :
    (wantField M copies party tag here width nbr).eval m row=(wantFor M copies party choice here width nbr).eval m row := by
  unfold wantField
  rw [eval_chooseField _ _ _ _ _ _ (Fintype.equivFin _ choice) fits (by omega)]
  rw [Equiv.symm_apply_apply]

theorem wantFor_blank (m : Memory W) (row : Word W) (choice : M.index) (here width nbr : Expr)
    (blank : width.eval m row=0) :
    (wantFor M copies party choice here width nbr).eval m row=0 := by
  simp [wantFor,Expr.eval,Comparison.test,blank]

theorem wantFor_read (m : Memory W) (row : Word W) (choice : M.index) (here width nbr : Expr)
    (place : Fin k↪Fin S) (loc other : Fin S) (ne : loc≠other)
    (live : width.eval m row≠0) (sites : S≤2^W)
    (measured : ∀i,(party i).eval m row=((place i).val:Word W))
    (atSite : here.eval m row=(loc.val:Word W)) (atOther : nbr.eval m row=(other.val:Word W)) :
    (wantFor M copies party choice here width nbr).eval m row=
      (optionWidths (fun a : PositiveDemand req choice.val.val=>physicalChord place (edge (req a.val)))
        (fun _=>copies*(M.packet choice).width) (orderedEnds loc other ne):Word W) := by
  have receipt:=lowBefore_read m row (fun a : PositiveDemand req choice.val.val=>edge (req a.val))
    place party .row here nbr (.lit (copies*(M.packet choice).width)) loc other ne _
    sites measured atSite atOther rfl
  simpa [wantFor,Expr.eval,Comparison.test,live] using receipt

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory

namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Hierarchy.ProtocolRAM
variable {M D base : ℕ}
/-- ABI following the captured menu and histograms: contiguous turn operands,
then all old neighbor widths, then all new neighbor widths. -/
def packetFields (pre : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (lowBefore : Fin D→Expr) :
    Fin (base+((M*3)*5+(D+D)))→Expr :=
  Fin.addCases pre (Fin.addCases (fun i=>gate (i.castAdd D))
    (Fin.addCases lowBefore (fun q=>gate (Fin.natAdd ((M*3)*5) q))))

@[simp] theorem packetFields_pre (pre : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (lowBefore : Fin D→Expr) (i : Fin base) :
    packetFields pre gate lowBefore (i.castAdd _)=pre i := by simp [packetFields]

@[simp] theorem packetFields_turn (pre : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (lowBefore : Fin D→Expr) (i : Fin ((M*3)*5)) :
    packetFields pre gate lowBefore (Fin.natAdd base (i.castAdd (D+D)))=gate (i.castAdd D) := by simp [packetFields]

@[simp] theorem packetFields_before (pre : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (lowBefore : Fin D→Expr) (i : Fin D) :
    packetFields pre gate lowBefore (Fin.natAdd base (Fin.natAdd ((M*3)*5) (i.castAdd D)))=lowBefore i := by simp [packetFields]

@[simp] theorem packetFields_after (pre : Fin base→Expr) (gate : Fin ((M*3)*5+D)→Expr) (lowBefore : Fin D→Expr) (i : Fin D) :
    packetFields pre gate lowBefore (Fin.natAdd base (Fin.natAdd ((M*3)*5) (Fin.natAdd D i)))=
      gate (Fin.natAdd ((M*3)*5) i) := by simp [packetFields,-Fin.natAdd_eq_addNat]

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
