import OAI.Hierarchy.DescentResetGroupingBounds
import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentInstalledNames
import OAI.Hierarchy.DescentResetPlacementPrice
import OAI.Hierarchy.DescentContactCodes
import OAI.Hierarchy.DescentContactNumbers

namespace OAI
/-! # The reset invoice with the actual dyadic good-base selection -/

namespace Hierarchy.DescentResetInvoice
open DescentGL DescentColonies DescentBaseVariance DescentChosenRouter
open DescentMixedRouter DescentContactTree
open scoped Classical BigOperators
noncomputable section

theorem directory_height {V A : Type*} [DecidableEq V] [Fintype A]
    (near : Finset V) {Δ Y : ℕ} (branch : 0<Δ) (rows : 0<Y)
    (degree : near.card≤Δ) (d id h : ℕ) (hub : V→Bool)
    (code : A ↪ ↥(DescentContacts.names near (fun v =>
      DescentContacts.fromNonhub Y d id (32*Nat.clog 2 (2*Δ)) h (hub v)))) :
    codeHeight A ≤ 36*Nat.clog 2 (2*Δ*Y) := by
  refine (height_bound _ ?_).trans (DescentContacts.nonhub_height near branch rows degree d id h hub)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective code code.injective

variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H]
    [Fintype A] [Field K] {k n h C₀ bits u : ℕ}

/-- The selected dyadic base circuits and the fallback choice appearing here
are concrete. On a core wire the fallback relay is possible precisely when
an original endpoint was marked. -/
theorem chosen_invoice (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) {pay scale price ε β : ℝ}
    (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (D : ℕ) (core : Finset I) (hops tetherHops : ℕ) (weight : V→Block k→ℝ)
    (hp : 0≤price) (hn : 0≤pay) (he : 0≤ε) (hb : 0≤β) (rate : price*pay=scale)
    (ordinary : ∀i∈core,∀s,¬P.hub (P.old s i).1)
    (inc : ∀p,load (P.old false) (fun i=> if i∈core then price*u else 0) p +
      load (P.old true) (fun i=> if i∈core then price*u else 0) p ≤ weight p.1 p.2)
    (fallback : ∀i∈badCore (selected P G hw pay hardware) core,
      edgeHops (selected P G hw pay hardware) i≤hops)
    (external : ∀i∉core,edgeHops (selected P G hw pay hardware) i≤tetherHops)
    (hub : (∑v,∑i,weight v i) ≤
      2*(price*∑_i∈core,(u:ℝ))+(β+1)*(price*∑_i∈coreᶜ,(u:ℝ))+ε)
    (span : scale*(∑v,(2:ℝ)^P.b v) ≤ 4*(ε+∑v,∑i,weight v i))
    (marked : (hops:ℝ)*(∑p∈validBases P.b P.keys,baseValue P.b P.depth weight P.L p)≤
      ε+∑v,∑i,weight v i) :
    price*((∑e,(network G hw u P.contact P.input P.site P.owner P.align
      (selected P G hw pay hardware) D).width e : ℕ):ℝ) ≤
      internalRate h C₀*(price*(∑_i∈core,(u:ℝ))+ε) +
        exteriorRate h C₀ β tetherHops*(price*∑_i∈coreᶜ,(u:ℝ)) :=
  installed_invoice (selected P G hw pay hardware) D core hops tetherHops
    P.b P.depth P.L P.keys (P.old false) (P.old true) weight hp hn he hb rate
    (named P G hw pay hardware) (per_base P G hw pay hardware) (flagged P G hw pay hardware core ordinary)
    inc fallback external hub span marked

end
end Hierarchy.DescentResetInvoice

end OAI
