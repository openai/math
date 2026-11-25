import OAI.Hierarchy.DescentPhysicalSiteVolume
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentResetWorldHistory
import OAI.Hierarchy.DescentBundleSeed
import OAI.Hierarchy.DescentScheduledBitHistory

namespace OAI
/-! # Every inherited node retains its original arity and operand lengths throughout the calendar -/
namespace Hierarchy.DescentKernelHistory.BitDescription
open Computability.BorderVNP.Crossing DescentSixParty DescentHostDirectory DescentInitialHost
open DescentBundleHistory DescentResetTrunks DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def WidthBound (B : BitDescription W) (M : ℕ) : Prop :=
  ∀v n,(B.recipe v).nodeBits n≤M

variable {B : BitDescription W} {M : ℕ}

theorem WidthBound.selected (old : B.WidthBound M) {I H : Type} [Fintype I]
    (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→H) (p : I→Profile G.C)
    (born : ∀i,8*(z i*(G.C+G.k+G.b+2))≤M) :
    (B.selected G pick z hz fit room pack p).WidthBound M := by
  intro v n
  rcases n with ⟨⟨u,hu⟩,n⟩
  rcases u with a | ⟨i,j⟩
  · exact old a n
  · exact (physical_role_nodeBits (W:=W.toWorld) (G:=G) (chosen:=pick) (z:=z)
      (room:=room) (p:=p) (old:=B.recipe) fit i j n).trans (born i)

theorem WidthBound.follow (normal : Normalize W) (old : B.WidthBound M) :
    (follow normal B).WidthBound M := by
  revert B
  induction normal with
  | done =>
    intro B old
    exact old
  | named W s e rest ih =>
    intro B old
    exact ih (B:=B.renamed s e) (fun v n=>old (s.symm v) n)
  | split W q m fit rest ih =>
    intro B old
    exact ih (B:=B.pieces m q fit) old
  | merge W V key flag k g rest ih =>
    intro B old
    apply ih (B:=B.coalesced key flag k g)
    rintro _ ⟨u,n⟩
    exact old u.val n

theorem WidthBound.scanned (old : B.WidthBound M) {u ε : ℝ} (G : PoweredGadget F) (he : 0≤ε)
    (T : StageInput W G u ε) (p : (T.result he).Choice) (born : 8*(T.z*(G.C+G.k+G.b+2))≤M) :
    (scanned he T B p).WidthBound M := by
  have transport {X Y : MarkedWorld F d P bits} (eqn : X=Y) (bb : BitDescription X)
      (h : bb.WidthBound M) : (cast (congrArg BitDescription eqn) bb).WidthBound M := by subst Y;exact h
  let rows := scannedRows he T
  exact transport (rows.state p).symm _ (old.selected G rows.pick (fun _=>T.z)
    (fun _=>T.unitPos) rows.fit (fun _=>le_refl T.z) rows.pack (rows.profile p) (fun _=>born))

theorem initial_width {k n : ℕ} (X : Catalyst.Approximation F k n) (R s : ℕ)
    (c : (initialGroup X R s).Choice) : (initial X R s c).WidthBound (3*s) :=
  fun v u=>initial_node_bits X R s c v u

theorem WidthBound.installed (old : B.WidthBound M)
    {H Q U : Type} [Fintype H] [Fintype Q] {L n : ℕ} (home : W.graph.Site→H)
    (group : Bool→W.graph.Edge→Q) (flag : H→Bool) {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
    (R : Network n (Bool×Q) (publicWidth group w)) (legacy sorted : R.Tables F)
    (key : W.graph.Edge↪Fin L) (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) R)
    (valid : ReadsBits R scalar r sorted) (relayRoom : ∀e,2*W.graph.width e≤M)
    (bankRoom : ∀v i,(r v).nodeBits i≤M) :
    (B.installed home group flag same R legacy sorted key scalar r valid).WidthBound M := by
  subst w
  intro v n
  rcases v with ⟨_|_,t⟩|v
  · rcases n with ⟨⟨v,rfl⟩,i⟩
    exact old v i
  · change (∑ _j : Fin 2, W.graph.width n.val) ≤ M
    simpa only [Fin.sum_univ_two, two_mul] using relayRoom n.val
  · exact bankRoom v n

theorem WidthBound.lane_reset (old : B.WidthBound M) {q ε : ℝ} {h C Ht L : ℕ}
    (Z : ResetInput W q ε h C Ht) (T : Z.Terminals) (key : W.graph.Edge↪Fin L)
    (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
    (cfg : ∀π,DescentRotor.Configures F Z.graph.arcs C Z.width π)
    (relays : ∀e,2*W.graph.width e≤M) (rotor : max 2 ((2+2*h*C)*Z.width)*p≤M) :
    (B.batchedReset Z T key m p hp fit cfg).WidthBound M := by
  apply old.installed
  · exact relays
  · intro v n
    change (∑_j : Fin (((Z.laneProgram key m p hp fit v).op n).arity),p)≤M
    simpa using (Nat.mul_le_mul_right p (Z.lane_arity key m p hp fit v n)).trans rotor

end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI
