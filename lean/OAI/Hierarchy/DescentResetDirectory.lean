import OAI.Hierarchy.DescentResetChosenBill

namespace OAI
/-! # Recovering local exceptional contact directories from the original routed items -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentBaseProfile DescentRouterSlots DescentMixedRouter
open DescentContactTree DescentContacts
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k n : ℕ} (P : Placement V I H A k (2^n))
local notation "Y" => (2^n : ℕ)

/-- At a fixed terminal a local cable is uniquely named by its other terminal.
No good-base output reservation can occur in this fiber. -/
def opposite (s : Bool) (t : H) (c : LinkId P.owner s (.inr t)) : H :=
  match c with
  | ⟨.inl _,hit⟩ => False.elim (by simp [Placement.owner,owner] at hit)
  | ⟨.inr p,_⟩ => if s then p.val.1 else p.val.2

theorem opposite_injective (s : Bool) (t : H) : Function.Injective (opposite P s t) := by
  rintro ⟨a|p,ap⟩ ⟨a'|p',ap'⟩ same
  · simp [Placement.owner,owner] at ap
  · simp [Placement.owner,owner] at ap
  · simp [Placement.owner,owner] at ap'
  · apply Subtype.ext
    apply congrArg Sum.inr
    apply Subtype.ext
    cases s
    · exact Prod.ext ((Sum.inr.inj ap).trans (Sum.inr.inj ap').symm) same
    · exact Prod.ext same ((Sum.inr.inj ap).trans (Sum.inr.inj ap').symm)

/-- Every such name has a concrete witnessing item in the original old wire
inventory, at exactly this root and its opposite port. -/
theorem opposite_realized (s : Bool) (t : H) (c : LinkId P.owner s (.inr t)) :
    ∃ i : Bad P.b P.depth P.L P.keys P.hub P.old,
      P.fall s (P.old s i.val)=t ∧ P.fall (!s) (P.old (!s) i.val)=opposite P s t c := by
  rcases c with ⟨a|p,root⟩
  · simp [Placement.owner,owner] at root
  · obtain ⟨i,_,eqn⟩ := Finset.mem_image.mp p.property
    have ends : (P.fall false (P.old false i.val),P.fall true (P.old true i.val))=p.val := eqn
    refine ⟨i,?_⟩
    cases s
    · have root' : p.val.1=t := Sum.inr.inj root
      exact ⟨(congrArg Prod.fst ends).trans root',congrArg Prod.snd ends⟩
    · have root' : p.val.2=t := Sum.inr.inj root
      exact ⟨(congrArg Prod.snd ends).trans root',congrArg Prod.fst ends⟩

/-- Certifying the geometry of each actual original item is enough to embed
the entire directory into the finite list of geometrically possible names. -/
def opposite_directory {Z : Type*} (code : H ↪ Z) (allowed : Finset Z)
    (s : Bool) (t : H) (fits : ∀i : Bad P.b P.depth P.L P.keys P.hub P.old,
      P.fall s (P.old s i.val)=t → code (P.fall (!s) (P.old (!s) i.val))∈allowed) :
    LinkId P.owner s (.inr t) ↪ ↥allowed where
  toFun c := ⟨code (opposite P s t c),by
    obtain ⟨i,root,target⟩ := opposite_realized P s t c
    simpa only [←target] using fits i root⟩
  inj' := fun _ _ eq => opposite_injective P s t (code.injective (congrArg Subtype.val eq))

/-- On a nonhub the height depends on the number of rows and on the old degree. -/
theorem fallback_nonhub_height (s : Bool) (t : H) {Δ : ℕ} (code : H ↪ V×Endpoint Y)
    (near : Finset V) (d id h : ℕ) (isHub : V→Bool) (degree : near.card≤Δ)
    (positive : 0<Δ) (rows : 0<Y)
    (fits : ∀i : Bad P.b P.depth P.L P.keys P.hub P.old,P.fall s (P.old s i.val)=t →
      code (P.fall (!s) (P.old (!s) i.val))∈names near
        (fun v=>fromNonhub Y d id (32*Nat.clog 2 (2*Δ)) h (isHub v))) :
    codeHeight (LinkId P.owner s (.inr t)) ≤ 36*Nat.clog 2 (2*Δ*Y) :=
  DescentResetInvoice.directory_height near positive rows degree d id h isHub
    (opposite_directory P code _ s t fits)

/-- At a merged hub the directory height may also depend on the fixed merge
and grouping exponents, which enter only the exterior coefficient. -/
theorem fallback_hub_height (s : Bool) (t : H) {Δ : ℕ} (code : H ↪ V×Endpoint Y)
    (near : Finset V) (id D f g : ℕ) (degree : near.card≤Δ)
    (fits : ∀i : Bad P.b P.depth P.L P.keys P.hub P.old, P.fall s (P.old s i.val)=t →
      code (P.fall (!s) (P.old (!s) i.val))∈names near
        (fun _=>terminals Y (possible (k-g) id D (g-f)))) :
    codeHeight (LinkId P.owner s (.inr t)) ≤ Nat.clog 2 (Δ*((D+1+2*2^(g-f))*Y)) := by
  have route := opposite_directory P code _ s t fits
  apply height_bound
  apply (Fintype.card_le_of_injective route route.injective).trans
  simpa only [Fintype.card_coe] using hub_names near degree Y k id D f g

variable {K : Type} [Field K] {h C₀ bits u : ℕ} (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)

/-- The selected rotor sends good items through no exceptional hops. Every
other old item traverses the directories of its two actual fallback terminals. -/
theorem selected_hops (i : I) :
    edgeHops (selected P G hw pay hardware) i =
      if useRotor P.b P.depth P.L P.keys P.hub P.old i then 0 else
        (P.fallbackBook false (P.fall false (P.old false i))).height +
        (P.fallbackBook true (P.fall true (P.old true i))).height := by
  by_cases paid : useRotor P.b P.depth P.L P.keys P.hub P.old i
  · have cable : P.contact i = Sum.inl (P.ticket ⟨i,paid⟩) := by
      unfold Placement.contact contact
      exact dite_eq_left paid
    rw [ite_eq_left paid]
    unfold edgeHops
    rw [cable]; rfl
  · obtain ⟨p,cable,ends⟩ : ∃ p : ↥(Seen P.b P.depth P.L P.keys P.hub P.old P.fall),
        P.contact i = Sum.inr p ∧ p.val = (P.fall false (P.old false i), P.fall true (P.old true i)) := by
      unfold Placement.contact contact
      rw [dite_eq_right paid]
      exact ⟨_,rfl,rfl⟩
    rw [ite_eq_right paid]
    unfold edgeHops
    rw [cable]
    change (P.fallbackBook false p.val.1).height + (P.fallbackBook true p.val.2).height = _
    rw [ends]

theorem core_hops (core : Finset I) (Δ : ℕ)
    (nonhub : ∀i∈core,∀s,(P.fallbackBook s (P.fall s (P.old s i))).height ≤
      36*Nat.clog 2 (2*Δ*Y)) :
    ∀i∈badCore (selected P G hw pay hardware) core,
      edgeHops (selected P G hw pay hardware) i≤DescentResetInvoice.nonhubHops Δ Y := by
  intro i hi
  have hc : i∈core := (Finset.mem_filter.mp hi).1
  have left := nonhub i hc false
  have right := nonhub i hc true
  rw [selected_hops]
  unfold DescentResetInvoice.nonhubHops
  split <;> omega

theorem tether_hops (core : Finset I) (maxDepth : ℕ)
    (heights : ∀i∉core,∀s,(P.fallbackBook s (P.fall s (P.old s i))).height≤ maxDepth) :
    ∀i∉core,edgeHops (selected P G hw pay hardware) i≤2*maxDepth := by
  intro i hi
  have left := heights i hi false
  have right := heights i hi true
  rw [selected_hops]
  split <;> omega

end
end Hierarchy.DescentChosenRouter

end OAI
