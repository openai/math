import OAI.Hierarchy.DescentPrivateRawLabels
import OAI.Hierarchy.DescentPrivateOldDonors
import OAI.Hierarchy.DescentLocalPrivateNames

namespace OAI
/-! # Finite local keys for all live private words in a real ordinary branch -/
namespace Hierarchy.DescentPrivateRawLabels
open DescentBundleHistory DescentSixParty DescentCableDonorNames DescentPackedOperand
open DescentKernelHistory DescentNetworkPartition Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C]
    {d k i p D K Z b₁ b₂ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (desc : BitDescription W)
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i j,W.graph.width (pick (i,j))=z i*G.b) (room : ∀i,z i≤Z) (prof : I→Profile G.C)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
variable (hp : 0<p) (sh : ∀u,Shape p (desc.recipe u)) (ed : ∀e,p∣W.graph.width e)
    (pin : ∀x,p∣bits x) (quantum : ∀i,p∣z i)
local notation "start" => physicalBits G W.toWorld pick z room prof desc.recipe
local notation "s0" => physicalShape W desc G pick z room prof hp sh ed pin quantum
local notation "incoming" => physicalDonor hp W desc G pick z room prof sh ed pin quantum
variable (a : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Site→T) (b : T→C)
variable (x₁ : T→EuclideanSpace ℝ (Fin b₁)) (x₂ : C→EuclideanSpace ℝ (Fin b₂))
    (ok₁ : ∀t,‖x₁ t‖≤1) (ok₂ : ∀t,‖x₂ t‖≤1)
local notation "loc" => (b∘a)
local notation "oldWire" => physical_multiple W G pick z prof ed quantum
local notation "mid" => quotient M a x₁ ok₁
local notation "r₁" => quotientBits M a x₁ ok₁ start
local notation "s₁" => quotientShape M a x₁ ok₁ start s0 oldWire
local notation "s₂" => quotientShape mid b x₂ ok₂ r₁ s₁ (fun e=>oldWire e.val)
local notation "pre" => WireWord M p ⊕ (WireWord M p ⊕ OccupiedWord M start s0 hp)
local notation "fibre" => (fun c : C => {z : pre // originHome M a start s0 hp b z=c})

variable (halo : Halo C W.graph.Site D)
    (rawHere : ∀e : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Edge,
      W.graph.src (DescentCableDonorNames.anchor pick e)∈halo.member
        (b (a ((GadgetNetwork.physical W.graph pick (branchWidth G z prof)).src e))))
    (oldHere : ∀u : W.graph.Site,u∈halo.member (b (a (.inl u))))
variable (slot : ∀u,DescentLocalPrivateNames.Slot ((sh u).recipe hp) ↪ Fin K)

private theorem prior_site (v : OccupiedWord M start s0 hp) : v.1=Sum.inl (incoming v).1 := by
  rcases v with ⟨v|j,h⟩
  · rfl
  · exact h.val.1.elim

def carried {c : C} (v : {w : OccupiedWord M start s0 hp //loc w.1=c}) : Fin D × Fin K :=
  let t:=incoming v.val
  have eqn : loc (.inl t.1)=c := (congrArg loc (prior_site desc pick z room prof hp sh ed pin quantum v.val)).symm.trans v.property
  (halo.slot c ⟨t.1,(congrArg (fun site => t.1∈halo.member site) eqn).mp (oldHere t.1)⟩,
    DescentLocalPrivateNames.firstAlias ((sh t.1).recipe hp) (slot t.1) t.2)

omit [Fintype T] [Fintype C] in
private theorem carried_inj {c : C} : Function.Injective
    (carried desc pick z room prof hp sh ed pin quantum a b halo oldHere slot (c:=c)) := by
  intro u v eqn
  let x:=incoming u.val
  let y:=incoming v.val
  have site : x.1=y.1 := congrArg Subtype.val ((halo.slot c).injective (congrArg Prod.fst eqn))
  have digit : DescentLocalPrivateNames.firstAlias ((sh x.1).recipe hp) (slot x.1) x.2=
      DescentLocalPrivateNames.firstAlias ((sh y.1).recipe hp) (slot y.1) y.2 := congrArg Prod.snd eqn
  have identify (x y : OccupiedWord N desc.recipe sh hp) (site : x.1=y.1)
      (digit : DescentLocalPrivateNames.firstAlias ((sh x.1).recipe hp) (slot x.1) x.2=
        DescentLocalPrivateNames.firstAlias ((sh y.1).recipe hp) (slot y.1) y.2) : x=y := by
    rcases x with ⟨i,s⟩
    rcases y with ⟨j,t⟩
    change i=j at site
    subst j
    exact congrArg (Sigma.mk i) ((DescentLocalPrivateNames.firstAlias _ (slot i)).injective digit)
  exact Subtype.ext ((incoming).injective (identify x y site digit))

local notation "rawAt" => LocalWire (W:=W) (G:=G) (p:=p) pick z prof loc
local notation "carriedAt" => (fun c : C => {w : OccupiedWord M start s0 hp //loc w.1=c})

def classify (c : C) : fibre c ↪ (rawAt c ⊕ (rawAt c ⊕ carriedAt c)) where
  toFun
    | ⟨.inl w,h⟩=>.inl ⟨w,h⟩
    | ⟨.inr (.inl w),h⟩=>.inr (.inl ⟨w,h⟩)
    | ⟨.inr (.inr v),h⟩=>.inr (.inr ⟨v,h⟩)
  inj' := by
    let forget : (rawAt c ⊕ (rawAt c ⊕ carriedAt c)) → pre :=
      Sum.elim (fun w=>.inl w.val) (Sum.elim (fun w=>.inr (.inl w.val)) (fun v=>.inr (.inr v.val)))
    rintro ⟨w|w|w,h⟩ ⟨u|u|u,h'⟩ eqn <;> exact Subtype.ext (congrArg forget eqn)

def privateKey (c : C) (peer : rawAt c→ℕ) : ((s₂ c).recipe hp).UsedWord ↪ Key :=
  let fromHistory:=doubleAt M a x₁ ok₁ start s0 oldWire hp b x₂ ok₂ c
  let pieces:=classify desc pick z room prof hp sh ed pin quantum a b c
  let rawKey:=capture A native S ready pick z hz fit prof loc halo rawHere hp (c:=c)
  let oldKey:=carried desc pick z room prof hp sh ed pin quantum a b halo oldHere slot (c:=c)
  let labels : (rawAt c ⊕ (rawAt c ⊕ carriedAt c)) ↪ Key :=
    { toFun:=Sum.elim (rawKey true peer) (Sum.elim (rawKey false peer) (fun v=>Key.carried (oldKey v).1.val (oldKey v).2.val))
      inj':=by
        rintro (w|w|v) (w'|w'|v') eqn
        · exact congrArg Sum.inl ((rawKey true peer).injective eqn)
        · cases (show Key.second _ _ _ _=Key.first _ _ _ _ from eqn)
        · cases (show Key.second _ _ _ _=Key.carried _ _ from eqn)
        · cases (show Key.first _ _ _ _=Key.second _ _ _ _ from eqn)
        · exact congrArg (fun t=>Sum.inr (Sum.inl t)) ((rawKey false peer).injective eqn)
        · cases (show Key.first _ _ _ _=Key.carried _ _ from eqn)
        · cases (show Key.carried _ _=Key.second _ _ _ _ from eqn)
        · cases (show Key.carried _ _=Key.first _ _ _ _ from eqn)
        · have pair : oldKey v=oldKey v' := Prod.ext (Fin.ext (Key.carried.inj eqn).1) (Fin.ext (Key.carried.inj eqn).2)
          exact congrArg (fun t=>Sum.inr (Sum.inr t)) (carried_inj desc pick z room prof hp sh ed pin quantum a b halo oldHere slot pair) }
  fromHistory.trans (pieces.trans labels)

local notation "keyAt" => privateKey A native S ready desc pick z hz fit room prof hp sh ed pin quantum
  a b x₁ x₂ ok₁ ok₂ halo rawHere oldHere slot
local notation "sourceOf" => doubleOrigin M a x₁ ok₁ start s0 oldWire hp b x₂ ok₂
local notation "origin" => doubleAt M a x₁ ok₁ start s0 oldWire hp b x₂ ok₂

theorem capture_key {c:C} (source:rawAt c) (peer:rawAt c→ℕ) (second:Bool)
    (h:((s₂ c).recipe hp).UsedWord)
    (selected:sourceOf ⟨c,h⟩=if second then .inl source.val else .inr (.inl source.val)) :
    keyAt c peer h=(if second then Key.second else Key.first)
      (root (W:=W) (G:=G) (p:=p) pick z prof loc halo rawHere source).val (peer source)
      (11*(old A native S ready pick z hz fit prof loc hp source).val+(DescentCableDonorNames.role source.val.1).val)
      source.val.2.val :=by
  cases second with
  | false =>
    have eqn:origin c h=⟨.inr (.inl source.val),source.property⟩:=Subtype.ext selected
    unfold privateKey
    simp only [Function.Embedding.trans_apply]
    rw [eqn]; rfl
  | true =>
    have eqn:origin c h=⟨.inl source.val,source.property⟩:=Subtype.ext selected
    unfold privateKey
    simp only [Function.Embedding.trans_apply]
    rw [eqn]; rfl

theorem inherited_key {c:C} (source:carriedAt c) (peer:rawAt c→ℕ) (h:((s₂ c).recipe hp).UsedWord)
    (selected:sourceOf ⟨c,h⟩=.inr (.inr source.val)) :
    let prior:=carried desc pick z room prof hp sh ed pin quantum a b halo oldHere slot source
    keyAt c peer h=Key.carried prior.1.val prior.2.val :=by
  have eqn:origin c h=⟨.inr (.inr source.val),source.property⟩:=Subtype.ext selected
  unfold privateKey
  simp only [Function.Embedding.trans_apply]
  rw [eqn]; rfl

theorem privateKey_tag (c : C) (peer : rawAt c→ℕ) (u : ((s₂ c).recipe hp).UsedWord) :
    ((privateKey A native S ready desc pick z hz fit room prof hp sh ed pin quantum
      a b x₁ x₂ ok₁ ok₂ halo rawHere oldHere slot c peer u).fields 0)<3 := by
  unfold privateKey
  simp only [Function.Embedding.trans_apply]
  cases classify desc pick z room prof hp sh ed pin quantum a b c (origin c u) with
  | inl w=>exact Nat.lt_succ_self 2
  | inr w=>
    cases w with
    | inl w=>exact (by decide : 1<3)
    | inr w=>exact (by decide : 0<3)

end
end Hierarchy.DescentPrivateRawLabels

end OAI
