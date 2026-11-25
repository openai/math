import OAI.Hierarchy.DescentArchiveRankData
import OAI.Hierarchy.DescentHiddenTransitions
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentResetEdgeTape

namespace OAI
/-! # Immutable hidden-coordinate names across the genuine p-wide reset -/

namespace Hierarchy.DescentHistoryOrder
open DescentKernelHistory DescentSixParty DescentRotor Computability.BorderVNP.Crossing
open DescentResetTrunks DescentRouterBank DescentNamedContact DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
variable {F X Y P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)

def trunkHidden (empty : ∀v,(bank v).Hidden→False) :
    Hidden _ (trunkBits N home group R key old bank)≃Hidden N old where
  toFun
    | ⟨.inl (false,_),.inl e⟩=>nomatch e
    | ⟨.inl (false,site),.inr ⟨⟨u,atSite⟩,h⟩⟩ => by
      subst site
      exact ⟨u,h⟩
    | ⟨.inl (true,_),e⟩=>nomatch e
    | ⟨.inr v,e⟩=>(empty v e).elim
  invFun a:=⟨.inl (false,home a.1),.inr ⟨⟨a.1,rfl⟩,a.2⟩⟩
  left_inv := by
    rintro ⟨⟨b,u⟩|v,h⟩
    · cases b
      · rcases h with impossible|⟨⟨w,eqn⟩,a⟩
        · exact nomatch impossible
        · cases eqn; rfl
      · exact nomatch h
    · exact (empty v h).elim
  right_inv := by rintro ⟨v,h⟩; rfl

variable {W : MarkedWorld F n P bits} (B : BitDescription W)
section Installation
variable (place : W.graph.Site→H) (inputs : Bool→W.graph.Edge→Q) (flags : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (A : Network d (Bool×Q) (publicWidth inputs w))
    (legacy sorted : A.Tables F) (e : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
    (r : SiteBits (U:=Y) A) (valid : ReadsBits A scalar r sorted)

def installedHidden (empty : ∀v,(r v).Hidden→False) (rank : SiteRank B) :
    SiteRank (B.installed place inputs flags same A legacy sorted e scalar r valid) := by
  subst w
  exact (trunkHidden W.graph place inputs A e B.recipe r empty).toEmbedding.trans rank

end Installation

variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z) (e : W.graph.Edge↪Fin L)
    (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p) (menu : ∀π,Configures F Z.graph.arcs C Z.width π)

def resetHidden (rank : SiteRank B) : SiteRank (B.batchedReset Z T e m p hp fit menu) :=
  installedHidden B T.home Z.placement.input T.hub (funext fun x=>(Z.allWidths x).symm) Z.bank
    Z.tables (Z.orderedBank e) e _ (Z.laneRecipe e m p hp fit) (Z.lane_valid e m p hp fit menu)
    (fun _ x=>nomatch x) rank



end
end Hierarchy.DescentHistoryOrder

end OAI
