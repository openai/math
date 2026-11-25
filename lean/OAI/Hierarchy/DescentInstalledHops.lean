import OAI.Hierarchy.DescentResetPublicDepth
import OAI.Hierarchy.DescentResetDirectory
import OAI.Hierarchy.DescentFineTerminals

namespace OAI
/-! # Actual selected-bank relay depth from the original network incidences -/

namespace Hierarchy.DescentFineTerminals
open DescentGL DescentColonies DescentContacts DescentContactTree DescentChosenRouter DescentMixedRouter
open DescentResetInvoice DescentBaseVariance DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
  {k n f g B Δ : ℕ} (P : Placement V I H A k (2^n))
local notation "Y" => (2^n : ℕ)
local notation "radius" => (32*Nat.clog 2 (2*Δ))
variable (near : V→Finset V) (mass : V→Block k→ℕ) (room : ∀v i,mass v i≤B)
variable (hub : V→Bool) (row : Bool→V×Block k→Fin (2^n)) (code : H ↪ V×Endpoint (2^n))
local notation "N" => name (D:=radius) (f:=f) (g:=g) near mass room (Placement.b P) hub (Placement.L P) row

/-- Instantiate the directory certificate at any actual old endpoint. The
only incidence facts used are common block, old adjacency, and absence of
hub-to-hub edges. All quantifiers are over items of the finite routed bank. -/
def realized_window (named : ∀s o,code (P.fall s o)=N s o)
    (fit : ∀v,P.b v≤k-f) (smooth : ∀v w,w∈near v→P.b v≤P.b w+radius)
    (full : ∀v,hub v=true→P.b v=k-f) (fg : f≤g) (gk : g≤k)
    (adj : ∀s i,(P.old (!s) i).1∈near (P.old s i).1)
    (block : ∀s i,(P.old (!s) i).2=(P.old s i).2)
    (single : ∀s i,¬(hub (P.old s i).1=true ∧ hub (P.old (!s) i).1=true))
    (s : Bool) (t : H) :
    LinkId P.owner s (.inr t) ↪ ↥(window (k:=k) (D:=radius) (f:=f) (g:=g) near hub (code t)) := by
  apply opposite_directory P code _ s t
  intro i root
  rw [←root,named,named]
  have reverse := adj (!s) i.val
  simp only [Bool.not_not] at reverse
  have geometry := neighbor_mem (D:=radius) near mass room P.b hub P.L row fit smooth full fg gk
    (adj s i.val) reverse (single s i.val) s (!s) (P.old s i.val).2
  have other : ((P.old (!s) i.val).1,(P.old s i.val).2)=P.old (!s) i.val :=
    Prod.ext rfl (block s i.val).symm
  simpa only [other,Prod.eta] using geometry

omit [Fintype V] in
/-- The bound holds on both halves of the board at every terminal, including
a terminal whose original items appeared only in the other orientation. -/
theorem directory_all {Z : Type} [Fintype Z] (z : V×Endpoint Y)
    (embed : Z ↪ ↥(window (k:=k) (D:=radius) (f:=f) (g:=g) near hub z))
    (positive : 0<Δ) (degree : ∀v,(near v).card≤Δ) :
    codeHeight Z≤ max (terminalDepth Δ Y f g false) (terminalDepth Δ Y f g true) := by
  have card := Fintype.card_le_of_injective embed embed.injective
  rw [Fintype.card_coe] at card
  apply (height_bound _ card).trans
  cases ordinary : z.2.2.isSome
  · apply le_trans _ (le_max_left ..)
    simpa [window,ordinary,terminalDepth] using
      Nat.clog_mono_right 2 (hub_names (near z.1) (degree z.1) Y k z.2.1.2 radius f g)
  · apply le_trans _ (le_max_right ..)
    simpa [window,ordinary,terminalDepth] using nonhub_height (near z.1) positive
      (Nat.two_pow_pos n) (degree z.1) z.2.1.1 z.2.1.2 (k-g) hub

theorem realized_height (named : ∀s o,code (P.fall s o)=N s o)
    (fit : ∀v,P.b v≤k-f) (smooth : ∀v w,w∈near v→P.b v≤P.b w+radius)
    (full : ∀v,hub v=true→P.b v=k-f) (fg : f≤g) (gk : g≤k)
    (adj : ∀s i,(P.old (!s) i).1∈near (P.old s i).1)
    (block : ∀s i,(P.old (!s) i).2=(P.old s i).2)
    (single : ∀s i,¬(hub (P.old s i).1=true ∧ hub (P.old (!s) i).1=true))
    (positive : 0<Δ) (degree : ∀v,(near v).card≤Δ) (s : Bool) (o : V×Block k) :
    codeHeight (LinkId P.owner s (.inr (P.fall s o))) ≤ terminalDepth Δ Y f g (!(hub o.1)) := by
  let t := P.fall s o
  let z := code t
  have embed := realized_window P near mass room hub row code named fit smooth full fg gk
    adj block single s t
  have card := Fintype.card_le_of_injective embed embed.injective
  rw [Fintype.card_coe] at card
  have invoice := height_bound _ card
  have same : code t=N s o := named s o
  cases h : hub o.1
  · apply invoice.trans
    simpa [same,name,window,h,terminalDepth] using
      nonhub_height (near o.1) positive (Nat.two_pow_pos n) (degree o.1)
        (leaf (D:=radius) (f:=f) near mass room P.b o.1 (rearrange P.L o.2))
        (group (leaf (D:=radius) (f:=f) near mass room P.b o.1 (rearrange P.L o.2)) (rearrange P.L o.2)) (k-g) hub
  · apply invoice.trans
    simpa [same,name,window,h,terminalDepth] using
      Nat.clog_mono_right 2 (hub_names (near o.1) (degree o.1) Y k
        (group (k-g) (rearrange P.L o.2)) radius f g)

variable {K : Type} [Field K] {h C₀ bits u : ℕ} (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)

/-- A canonical whole-roster book may have extra unused leaves. Their depths
are paid using the complete roster bound, separately at hubs and nonhubs. -/
theorem installed_hops_book (named : ∀s o,code (P.fall s o)=N s o)
    (depths : ∀s t,(P.fallbackBook s t).height≤terminalDepth Δ Y f g (code t).2.2.isSome)
    (core : Finset I) (ordinary : ∀i∈core,∀s,hub (P.old s i).1=false) :
    (∀i∈badCore (selected P G hw pay hardware) core,
      edgeHops (selected P G hw pay hardware) i≤nonhubHops Δ Y) ∧
    ∀i∉core,edgeHops (selected P G hw pay hardware) i≤
      2*max (terminalDepth Δ Y f g false) (terminalDepth Δ Y f g true) := by
  constructor
  · apply core_hops P G hw pay hardware
    intro i hi s
    simpa [named,name,ordinary i hi s,terminalDepth] using depths s (P.fall s (P.old s i))
  · apply tether_hops P G hw pay hardware
    intro i _ s
    apply (depths s (P.fall s (P.old s i))).trans
    cases (code (P.fall s (P.old s i))).2.2.isSome
    · exact le_max_left ..
    · exact le_max_right ..

/-- For the selected physical bank a core wire needs two nonhub trees at most.
The other wires can also use a merged-hub tree, whose extra depth is charged
only to the exterior coefficient. -/
theorem installed_hops (named : ∀s o,code (P.fall s o)=N s o)
    (fit : ∀v,P.b v≤k-f) (smooth : ∀v w,w∈near v→P.b v≤P.b w+radius)
    (full : ∀v,hub v=true→P.b v=k-f) (fg : f≤g) (gk : g≤k)
    (adj : ∀s i,(P.old (!s) i).1∈near (P.old s i).1)
    (block : ∀s i,(P.old (!s) i).2=(P.old s i).2)
    (single : ∀s i,¬(hub (P.old s i).1=true ∧ hub (P.old (!s) i).1=true))
    (positive : 0<Δ) (degree : ∀v,(near v).card≤Δ) (core : Finset I)
    (ordinary : ∀i∈core,∀s,hub (P.old s i).1=false)
    (book : ∀s t,(P.fallbackBook s t).height≤codeHeight (LinkId P.owner s (.inr t)) := by intros; exact le_rfl) :
    (∀i∈badCore (selected P G hw pay hardware) core,
      edgeHops (selected P G hw pay hardware) i≤DescentResetInvoice.nonhubHops Δ Y) ∧
    ∀i∉core,edgeHops (selected P G hw pay hardware) i≤
      2*max (terminalDepth Δ Y f g false) (terminalDepth Δ Y f g true) := by
  have heights := realized_height P near mass room hub row code named fit smooth full fg gk
    adj block single positive degree
  constructor
  · apply core_hops P G hw pay hardware
    intro i hi s
    simpa [ordinary i hi s,terminalDepth] using (book s _).trans (heights s (P.old s i))
  · apply tether_hops P G hw pay hardware
    intro i _ s
    apply ((book s _).trans (heights s (P.old s i))).trans
    cases h : !(hub (P.old s i).1)
    · exact le_max_left ..
    · exact le_max_right ..


/-- Pay the physical installed network with the dyadic terminal directories.
The exceptional core price contains no hub-to-group size ratio. -/
theorem reset_invoice (named : ∀s o,code (P.fall s o)=N s o)
    (fit : ∀v,P.b v≤k-f) (smooth : ∀v w,w∈near v→P.b v≤P.b w+radius)
    (full : ∀v,hub v=true→P.b v=k-f) (tag : ∀v,P.hub v ↔ hub v=true)
    (fg : f≤g) (gk : g≤k)
    (adj : ∀s i,(P.old (!s) i).1∈near (P.old s i).1)
    (block : ∀s i,(P.old (!s) i).2=(P.old s i).2)
    (single : ∀s i,¬(hub (P.old s i).1=true ∧ hub (P.old (!s) i).1=true))
    (branch : 0<Δ) (degree : ∀v,(near v).card≤Δ) (core : Finset I)
    (ordinary : ∀i∈core,∀s,hub (P.old s i).1=false)
    (level : ℕ) (weight : V→Block k→ℝ) {price scale ε β : ℝ}
    (pp : 0≤price) (py : 0≤pay) (he : 0≤ε) (hb : 0≤β) (rate : price*pay=scale)
    (inc : ∀p,load (P.old false) (fun i=>if i∈core then price*u else 0) p +
      load (P.old true) (fun i=>if i∈core then price*u else 0) p≤weight p.1 p.2)
    (amount : (∑v,∑i,weight v i) ≤
      2*(price*∑_i∈core,(u:ℝ))+(β+1)*(price*∑_i∈coreᶜ,(u:ℝ))+ε)
    (span : scale*(∑v,(2:ℝ)^P.b v)≤4*(ε+∑v,∑i,weight v i))
    (marked : (nonhubHops Δ Y:ℝ)*(∑p∈validBases P.b P.keys,baseValue P.b P.depth weight P.L p)≤
      ε+∑v,∑i,weight v i)
    (book : ∀s t,(P.fallbackBook s t).height≤codeHeight (LinkId P.owner s (.inr t)) := by intros; exact le_rfl) :
    let ht := 2*max (terminalDepth Δ Y f g false) (terminalDepth Δ Y f g true)
    price*((∑e,(network G hw u P.contact P.input P.site P.owner P.align
      (selected P G hw pay hardware) level).width e : ℕ):ℝ)≤
      internalRate h C₀*(price*(∑_i∈core,(u:ℝ))+ε)+
      exteriorRate h C₀ β ht*(price*∑_i∈coreᶜ,(u:ℝ)) := by
  have paths := installed_hops P near mass room hub row code G hw pay hardware named
    fit smooth full fg gk adj block single branch degree core ordinary book
  exact chosen_invoice P G hw hardware level core (nonhubHops Δ Y) _ weight pp py he hb rate
    (fun i hi s bad=>by simpa only [ordinary i hi s,Bool.false_eq_true] using (tag _).mp bad)
    inc paths.1 paths.2 amount span marked

end
end Hierarchy.DescentFineTerminals

end OAI
