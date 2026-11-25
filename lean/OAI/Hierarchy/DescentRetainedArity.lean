import OAI.Hierarchy.DescentPhysicalSiteVolume
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentResetWorldHistory
import OAI.Hierarchy.DescentBundleSeed
import OAI.Hierarchy.DescentScheduledBitHistory

namespace OAI
/-! # The number of arguments of each real node throughout the calendar -/
namespace Hierarchy.DescentKernelHistory.BitDescription
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.GadgetNetwork DescentHostDirectory DescentInitialHost
open DescentBundleHistory DescentResetTrunks DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def ArityBound (B : BitDescription W) (M : ℕ) : Prop :=
  ∀v n,(B.recipe v).arity n≤M

variable {B : BitDescription W} {M : ℕ}

theorem ArityBound.selected (old : B.ArityBound M) {I H : Type} [Fintype I]
    (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→H) (p : I→Profile G.C)
    (born : 8≤M) :
    (B.selected G pick z hz fit room pack p).ArityBound M := by
  intro v n
  rcases n with ⟨⟨u,hu⟩,n⟩
  rcases u with a | ⟨i,j⟩
  · exact old a n
  · change Fintype.card (RolePort j)≤M
    exact (physical_role_arity j).trans born


theorem ArityBound.follow (normal : Normalize W) (old : B.ArityBound M) :
    (follow normal B).ArityBound M := by
  revert B
  induction normal with
  | done =>
    intro B old
    exact old
  | named W s e rest ih =>
    intro B old
    exact ih (B:=B.renamed s e) (fun v n => old (s.symm v) n)
  | split W q m fit rest ih =>
    intro B old
    exact ih (B:=B.pieces m q fit) old
  | merge W V key flag k g rest ih =>
    intro B old
    apply ih (B:=B.coalesced key flag k g)
    rintro _ ⟨u,n⟩
    exact old u.val n

theorem ArityBound.scanned (old : B.ArityBound M) {u ε : ℝ} (G : PoweredGadget F) (he : 0≤ε)
    (T : StageInput W G u ε) (p : (T.result he).Choice) (born : 8≤M) :
    (scanned he T B p).ArityBound M := by
  have transport {X Y : MarkedWorld F d P bits} (eqn : X=Y) (bb : BitDescription X)
      (h : bb.ArityBound M) : (cast (congrArg BitDescription eqn) bb).ArityBound M := by subst Y;exact h
  let rows := scannedRows he T
  exact transport (rows.state p).symm _ (old.selected G rows.pick (fun _ => T.z)
    (fun _ => T.unitPos) rows.fit (fun _ => le_refl T.z) rows.pack (rows.profile p) born)

theorem initial_arity_bound {k n : ℕ} (X : Catalyst.Approximation F k n) (R s : ℕ)
    (c : (initialGroup X R s).Choice) : (initial X R s c).ArityBound 3 :=
  fun v u=>initial_arity X R s c v u

theorem ArityBound.installed (old : B.ArityBound M)
    {H Q U : Type} [Fintype H] [Fintype Q] {L n : ℕ} (home : W.graph.Site→H)
    (group : Bool→W.graph.Edge→Q) (flag : H→Bool) {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
    (R : Network n (Bool×Q) (publicWidth group w)) (legacy sorted : R.Tables F)
    (key : W.graph.Edge↪Fin L) (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) R)
    (valid : ReadsBits R scalar r sorted) (relayRoom : 2≤M)
    (bankRoom : ∀v i,(r v).arity i≤M) :
    (B.installed home group flag same R legacy sorted key scalar r valid).ArityBound M := by
  subst w
  intro v n
  rcases v with ⟨_|_,t⟩|v
  · rcases n with ⟨⟨v,rfl⟩,i⟩
    exact old v i
  · exact relayRoom
  · exact bankRoom v n

theorem ArityBound.lane_reset (old : B.ArityBound M) {q ε : ℝ} {h C Ht L : ℕ}
    (Z : ResetInput W q ε h C Ht) (T : Z.Terminals) (key : W.graph.Edge↪Fin L)
    (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
    (cfg : ∀π,DescentRotor.Configures F Z.graph.arcs C Z.width π)
    (relays : 2≤M) (rotor : max 2 ((2+2*h*C)*Z.width)≤M) :
    (B.batchedReset Z T key m p hp fit cfg).ArityBound M := by
  apply old.installed
  · exact relays
  · intro v n
    exact (Z.lane_arity key m p hp fit v n).trans rotor

end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI
