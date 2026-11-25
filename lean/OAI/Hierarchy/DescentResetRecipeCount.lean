import OAI.Hierarchy.DescentResetWorldHistory

namespace OAI
/-! # The exact number of surviving and newly installed bit-recipe nodes at a reset -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentResetTrunks DescentRouterBank DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {F X Y P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)

omit [Fintype Q] in
/-- The old gathered tables retain each site once. Every former edge produces one finite
word equality on the relay, and every configured bank site supplies its actual program. -/
theorem trunk_node_count :
    (∑v,Fintype.card ((trunkBits N home group R key old bank v).Node)) =
      (∑u,Fintype.card (old u).Node)+Fintype.card N.Edge+∑v,Fintype.card (bank v).Node := by
  let M := DescentResetTrunks.network N home group R
  have primary (h : H) : Fintype.card ((trunkBits N home group R key old bank (.inl (false,h))).Node)=
      ∑u : Fibre home h,Fintype.card (old u.val).Node := by
    change Fintype.card (Σu : Fibre home h,(oldGather N home group R key old h u).Node)=_
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    rintro ⟨v,rfl⟩ _
    rfl
  have grouped : (∑h,∑u : Fibre home h,Fintype.card (old u.val).Node)=∑u,Fintype.card (old u).Node := by
    rw [←Fintype.sum_sigma' (fun h (u : Fibre home h)=>Fintype.card (old u.val).Node)]
    exact (Equiv.sigmaFiberEquiv home).sum_comp (fun u=>Fintype.card (old u).Node)
  have relays : (∑h,Fintype.card (Fibre (moved N home) h))=Fintype.card N.Edge := by
    rw [←Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (moved N home))
  change (∑v : (Bool×H)⊕R.Site,Fintype.card ((trunkBits N home group R key old bank v).Node))=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  simp_rw [primary]
  change ((∑h,Fintype.card (Fibre (moved N home) h))+(∑h,∑u : Fibre home h,Fintype.card (old u.val).Node))+
    (∑v,Fintype.card (bank v).Node)=_
  rw [relays,grouped,Nat.add_comm (Fintype.card N.Edge)]

namespace BitDescription
variable {W : MarkedWorld F n P bits} (B : BitDescription W) (place : W.graph.Site→H)
    (groupAt : Bool→W.graph.Edge→Q) (hub : H→Bool)

omit [Fintype Q] in
/-- Eliminating the width cast retains the concrete type of every recipe node. -/
theorem installed_node_count {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
    (board : Network d (Bool×Q) (publicWidth groupAt w)) (legacy sorted : board.Tables F)
    (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board)
    (valid : ReadsBits board scalar prog sorted) :
    (∑v,Fintype.card (((B.installed place groupAt hub same board legacy sorted ids scalar prog valid).recipe v).Node))=
      (∑v,Fintype.card (B.recipe v).Node)+Fintype.card W.graph.Edge+∑v,Fintype.card (prog v).Node := by
  subst w
  exact trunk_node_count W.graph place groupAt board ids B.recipe prog

variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z)
variable (ids : W.graph.Edge↪Fin L)

theorem fromBank_node_count (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) Z.bank)
    (valid : ReadsBits Z.bank scalar prog (Z.orderedBank ids)) :
    (∑v,Fintype.card (((B.fromBank Z T ids scalar prog valid).recipe v).Node))=
      (∑v,Fintype.card (B.recipe v).Node)+Fintype.card W.graph.Edge+∑v,Fintype.card (prog v).Node :=
  installed_node_count B T.home Z.placement.input T.hub (funext fun e=>(Z.allWidths e).symm)
    Z.bank Z.tables (Z.orderedBank ids) ids scalar prog valid

end BitDescription
end
end Hierarchy.DescentKernelHistory

end OAI
