import OAI.Hierarchy.DescentOrdinaryLocalBirth
import OAI.Hierarchy.DescentPackedLocalAtoms

namespace OAI
/-! # Occupancy of the physical donor and six-party node slots -/

namespace Hierarchy.DescentOrdinaryLocalBirth
open DescentPackedLocalAtoms DescentSIMDLookup
open DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing DescentNetworkPartition
open DescentCableDonorNames DescentSharedCableNames
open scoped Classical
noncomputable section
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C]
    {d k i D K Z d₁ d₂ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (desc : BitDescription W) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (room : ∀i,z i≤Z) (prof : I→Profile G.C) (picked : ∀i,pick (i,0)∈W.core)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
local notation "r₀" => physicalBits G W.toWorld pick z room prof desc.recipe
variable (a : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Site→T) (b : T→C)
variable (x₁ : T→EuclideanSpace ℝ (Fin d₁)) (x₂ : C→EuclideanSpace ℝ (Fin d₂))
    (ok₁ : ∀t,‖x₁ t‖≤1) (ok₂ : ∀t,‖x₂ t‖≤1)
local notation "mid" => quotient M a x₁ ok₁
local notation "r₁" => quotientBits M a x₁ ok₁ r₀
local notation "r₂" => quotientBits mid b x₂ ok₂ r₁
local notation "loc" => (b∘a)
variable (halo : Halo C W.graph.Site D)
    (oldHere : ∀u : W.graph.Site,u∈halo.member (b (a (.inl u))))
    (newHere : ∀i j,W.graph.src (pick (i,0))∈halo.member (b (a (.inr (i,j)))))
    (oldRank : ∀u,(desc.recipe u).Node ↪ Fin K)


/-- These are the selected old-site and matched outgoing slots in the receiver
row. Both use the source donor's coordinates in the same physical halo. -/
def oldSlot (c : C) (u : W.graph.Site) (h : loc (.inl u)=c) : Fin D :=
  halo.slot c ⟨u,h ▸ oldHere u⟩

def birthSlot (c : C) (i : I) (j : Fin 6) (h : loc (.inr (i,j))=c) : Fin D :=
  halo.slot c ⟨W.graph.src (pick (i,0)),h ▸ newHere i j⟩

def outgoingSlot (i : I) : Fin A.cap :=
  Stage.outgoing A native S ready ⟨pick (i,0),A.quantum_positive _ (picked i)⟩

structure CandidateData (D K cap : ℕ) where
  oldCount : Fin D → ℕ
  born : Fin D → Fin cap → Fin 6 → Bool

def CandidateData.active {cap : ℕ} (tab : CandidateData D K cap) (j : Fin (Width D K cap)) : Cell 1 :=
  let (donor,body) := finProdFinEquiv.symm j
  match finSumFinEquiv.symm body with
  | Sum.inl (old : Fin K) => if old.val<tab.oldCount donor then 1 else 0
  | Sum.inr (pair : Fin (cap*6)) =>
      let (slot,role):=finProdFinEquiv.symm pair
      if tab.born donor slot role then 1 else 0

variable (c : C) (tab : CandidateData D K A.cap)
    (oldCoverage : ∀(d : Fin D) (j : Fin K), j.val<tab.oldCount d ↔
      ∃ (u : W.graph.Site) (h : b (a (.inl u))=c) (n : (desc.recipe u).Node),
        oldSlot pick z prof a b halo oldHere c u h=d ∧ oldRank u n=j)
    (birthCoverage : ∀d t j,tab.born d t j=true ↔
      ∃ (i : I) (h : b (a (.inr (i,j)))=c),
        birthSlot pick z prof a b halo newHere c i j h=d ∧ outgoingSlot A native S ready pick picked i=t)

include oldCoverage birthCoverage in
theorem active_iff (j : Fin (Width D K A.cap)) :
    tab.active j≠0 ↔ ∃ n : (r₂ c).Node,
      short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c n=j := by
  let e:=roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c
  let f:=book A native S ready desc pick z room prof picked a b halo oldHere newHere oldRank c
  have transfer : (∃n : (r₂ c).Node,f (e n)=j) ↔ ∃r,f r=j := by
    constructor
    · rintro ⟨n,hn⟩
      exact ⟨e n,hn⟩
    · rintro ⟨r,hr⟩
      exact ⟨e.symm r, by simpa only [e.apply_symm_apply] using hr⟩
  change _ ↔ ∃n : (r₂ c).Node,f (e n)=j
  rw [transfer]
  obtain ⟨⟨d,s⟩,rfl⟩:=(finProdFinEquiv (m:=D) (n:=K+A.cap*6)).surjective j
  obtain ⟨body,rfl⟩:=(finSumFinEquiv (m:=K) (n:=A.cap*6)).surjective s
  rcases body with old | born
  · simp only [CandidateData.active,Equiv.symm_apply_apply,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]
    constructor
    · intro yes
      rcases (oldCoverage d old).mp yes with ⟨u,h,n,hu,hn⟩
      refine ⟨⟨⟨.inl u,h⟩,n⟩, ?_⟩
      exact congrArg (finProdFinEquiv (m:=D) (n:=K+A.cap*6)) (Prod.ext hu
        (congrArg (fun q : Fin K => (finSumFinEquiv (n:=A.cap*6)) (.inl q)) hn))
    · rintro ⟨⟨⟨u|⟨i,t⟩,h⟩,n⟩,hu⟩
      all_goals
        obtain ⟨hd,hb⟩ := Prod.mk.inj ((finProdFinEquiv (m:=D) (n:=K+A.cap*6)).injective hu)
        have tags := (finSumFinEquiv (m:=K) (n:=A.cap*6)).injective hb
      · exact (oldCoverage d old).mpr ⟨u,h,n,hd,Sum.inl.inj tags⟩
      · cases tags
  · obtain ⟨⟨slot,role⟩,rfl⟩:=(finProdFinEquiv (m:=A.cap) (n:=6)).surjective born
    simp only [CandidateData.active,Equiv.symm_apply_apply,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]
    constructor
    · intro yes
      rcases (birthCoverage d slot role).mp yes with ⟨i,h,hd,hs⟩
      refine ⟨⟨⟨.inr (i,role),h⟩,()⟩,?_⟩
      exact congrArg (finProdFinEquiv (m:=D) (n:=K+A.cap*6)) (Prod.ext hd
        (congrArg (fun s : Fin A.cap =>
          (finSumFinEquiv (m:=K)) (.inr (finProdFinEquiv (s,role)))) hs))
    · rintro ⟨⟨⟨u|⟨i,t⟩,h⟩,n⟩,hu⟩
      all_goals
        obtain ⟨hd,hb⟩ := Prod.mk.inj ((finProdFinEquiv (m:=D) (n:=K+A.cap*6)).injective hu)
        have tags := (finSumFinEquiv (m:=K) (n:=A.cap*6)).injective hb
      · cases tags
      · obtain ⟨hs,ht⟩ := Prod.mk.inj ((finProdFinEquiv (m:=A.cap) (n:=6)).injective (Sum.inr.inj tags))
        subst t
        exact (birthCoverage d slot role).mpr ⟨i,h,hd,hs⟩

include oldCoverage birthCoverage in
theorem refreshed {bits K' : ℕ} (small : Fintype.card (r₂ c).Node≤K')
    (field : Fin (Width D K A.cap) → Cell bits) (n : (r₂ c).Node) :
    let index:=(compact A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c n).castLE small
    let addr:=short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c n
    DescentSIMDLookup.digit bits index.val
      (DescentPackedLocalAtoms.pack bits (Width D K A.cap) K'
        (DescentSIMDLookup.encode 1 (Width D K A.cap) tab.active)
        (DescentSIMDLookup.encode bits (Width D K A.cap) field)).val=(field addr).val := by
  let ids := short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c
  have occupied : ∀ j, tab.active j ≠ 0 ↔ ∃ node, ids node = j :=
    active_iff A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c
      tab oldCoverage birthCoverage
  simpa only [compact, ids] using
    (DescentPackedLocalAtoms.true_digit ids small tab.active field occupied n)

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI
