import OAI.Hierarchy.DescentOrdinaryCandidateAtoms
import OAI.Hierarchy.DescentPackedActorMask

namespace OAI
/-! # Old scalar counts and receiving venue addresses in a packed actor panel -/

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



variable (c : C)

def donorAt (j : Fin D) : Option W.graph.Site :=
  if h : ∃u : {u : W.graph.Site // u∈halo.member c},halo.slot c u=j then
    some h.choose.val
  else none

omit [Field F] [Fintype C] in
theorem donorAt_eq {j : Fin D} {u : W.graph.Site} :
    donorAt halo c j=some u ↔ ∃h : u∈halo.member c,halo.slot c ⟨u,h⟩=j := by
  classical
  unfold donorAt
  split
  next good =>
    let t:={v : W.graph.Site // v∈halo.member c}
    let actor : t:=good.choose
    have eqn : halo.slot c actor=j := good.choose_spec
    constructor
    · intro eqn'
      have vEq : actor.val=u:=Option.some.inj eqn'
      subst u;exact ⟨actor.property,eqn⟩
    · rintro ⟨h,hs⟩
      exact congrArg (fun x : t=>some x.val) ((halo.slot c).injective (eqn.trans hs.symm))
  next absent =>
    constructor
    · intro e;cases e
    · rintro ⟨h,hs⟩
      exact (absent ⟨⟨u,h⟩,hs⟩).elim

/-- The previously issued node count is read only when the prior donor exists.
The bounded source panel also names a target for each old or new actor. -/
def CandidateData.fromAddresses {n m cap : ℕ} (wanted : Cell n) (address : Fin (DescentPackedActorMask.actors D cap)→Cell n)
    (count : Fin D→Cell m) : CandidateData D K cap where
  oldCount d:=if address (DescentPackedActorMask.oldAddress cap d)=wanted then (count d).val else 0
  born d slot j:=decide (address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (slot,j)))=wanted)

variable {n m : ℕ} (wanted : Cell n) (address : Fin (DescentPackedActorMask.actors D A.cap)→Cell n)
    (count : Fin D→Cell m)
    (count_read : ∀d,(count d).val=((donorAt halo c d).map (fun u=>Fintype.card (desc.recipe u).Node)).getD 0)
    (target_old : ∀d,address (DescentPackedActorMask.oldAddress A.cap d)=wanted ↔
      ∃u,donorAt halo c d=some u ∧ b (a (.inl u))=c)
    (target_new : ∀d slot j,address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (slot,j)))=wanted ↔
      ∃i,donorAt halo c d=some (W.graph.src (pick (i,0))) ∧
        outgoingSlot A native S ready pick picked i=slot ∧ b (a (.inr (i,j)))=c)
    (old_dense : ∀u (j : Fin K),j.val<Fintype.card (desc.recipe u).Node ↔ ∃n,oldRank u n=j)

include count_read target_old old_dense in
omit [Fintype T] [Fintype C] in
theorem measured_old (d : Fin D) (j : Fin K) :
    j.val < (CandidateData.fromAddresses (K:=K) wanted address count).oldCount d ↔
    ∃ (u : W.graph.Site) (h : b (a (.inl u))=c) (n : (desc.recipe u).Node),
      oldSlot pick z prof a b halo oldHere c u h=d ∧ oldRank u n=j := by
  change (j.val < if address (DescentPackedActorMask.oldAddress A.cap d)=wanted then (count d).val else 0) ↔ _
  constructor
  · intro lt
    by_cases yes : address (DescentPackedActorMask.oldAddress A.cap d)=wanted
    · rw [ite_eq_left yes] at lt
      obtain ⟨u,source,dest⟩:=(target_old d).mp yes
      rw [count_read d,source] at lt
      obtain ⟨node,rank⟩:=(old_dense u j).mp lt
      obtain ⟨_,donor⟩ := (donorAt_eq halo c).mp source
      exact ⟨u,dest,node,donor,rank⟩
    · rw [ite_eq_right yes] at lt
      exact (Nat.not_lt_zero _ lt).elim
  · rintro ⟨u,dest,node,donor,rank⟩
    have source : donorAt halo c d=some u := (donorAt_eq halo c).mpr ⟨dest ▸ oldHere u,donor⟩
    rw [ite_eq_left ((target_old d).mpr ⟨u,source,dest⟩),count_read d,source]
    exact (old_dense u j).mpr ⟨node,rank⟩

include target_new in
omit [Fintype T] [Fintype C] in
theorem measured_born (d : Fin D) (slot : Fin A.cap) (j : Fin 6) :
    (CandidateData.fromAddresses (K:=K) wanted address count).born d slot j=true ↔
    ∃ (i : I) (h : b (a (.inr (i,j)))=c),
       birthSlot pick z prof a b halo newHere c i j h=d ∧ outgoingSlot A native S ready pick picked i=slot := by
  change (decide (address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (slot,j)))=wanted)=true) ↔ _
  rw [decide_eq_true_eq,target_new d slot j]
  constructor
  · rintro ⟨i,donor,hdest,h⟩
    obtain ⟨_,slotEq⟩ := (donorAt_eq halo c).mp donor
    exact ⟨i,h,slotEq,hdest⟩
  · rintro ⟨i,h,hd,hs⟩
    exact ⟨i,(donorAt_eq halo c).mpr ⟨h ▸ newHere i j,hd⟩,hs,h⟩

theorem issued_mask (alive : wanted≠0) :
    DescentPackedActorMask.occupied D K A.cap m
      (DescentPackedActorMask.target n _ wanted (encode n _ address)) (encode m D count)=
      encode 1 _ (CandidateData.fromAddresses (K:=K) wanted address count).active := by
  unfold DescentPackedActorMask.occupied
  apply congrArg (encode 1 (Width D K A.cap))
  funext j
  obtain ⟨⟨donor,s⟩,rfl⟩ := (finProdFinEquiv (m:=D) (n:=K+A.cap*6)).surjective j
  obtain ⟨body,rfl⟩ := (finSumFinEquiv (m:=K) (n:=A.cap*6)).surjective s
  rcases body with old | born
  · by_cases h : address (DescentPackedActorMask.oldAddress A.cap donor)=wanted <;>
      simp [DescentPackedActorMask.target,DescentPackedActorMask.bitAt,
        CandidateData.active,CandidateData.fromAddresses,alive,h]
  · obtain ⟨⟨slot,role⟩,rfl⟩ := (finProdFinEquiv (m:=A.cap) (n:=6)).surjective born
    by_cases h : address (DescentPackedActorMask.bornAddress donor (finProdFinEquiv (slot,role)))=wanted <;>
      simp [DescentPackedActorMask.target,DescentPackedActorMask.bitAt,
        CandidateData.active,CandidateData.fromAddresses,alive,h]

include count_read target_old target_new old_dense in
theorem venue_digit {s K'} (alive : wanted≠0) (small : Fintype.card (r₂ c).Node≤K')
    (field : Fin (Width D K A.cap)→Cell s) (u : (r₂ c).Node) :
    let output:=compact A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c u
    let prior:=short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c u
    let capMask:=DescentPackedActorMask.occupied D K A.cap m
      (DescentPackedActorMask.target n _ wanted (encode n _ address)) (encode m D count)
    digit s output.val (DescentPackedLocalAtoms.pack s _ K' capMask (encode s _ field)).val=(field prior).val := by
  dsimp only
  rw [issued_mask (K:=K) A wanted address count alive]
  refine refreshed A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c
    (CandidateData.fromAddresses (K:=K) wanted address count) ?_ ?_ small field u
  · intro donor j
    apply measured_old (count_read:=count_read) (target_old:=target_old) (old_dense:=old_dense)
  · intro donor slot role
    apply measured_born (target_new:=target_new)

theorem old_dense_of_equiv {X : Type} [Fintype X] (num : X≃Fin (Fintype.card X)) (room : Fintype.card X≤K)
    (j : Fin K) : j.val<Fintype.card X ↔ ∃x,(num x).castLE room=j := by
  constructor
  · intro lt
    refine ⟨num.symm ⟨j.val,lt⟩,Fin.ext ?_⟩
    simp only [Fin.val_castLE,Equiv.apply_symm_apply]
  · rintro ⟨u,rfl⟩
    exact (num u).isLt

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI
