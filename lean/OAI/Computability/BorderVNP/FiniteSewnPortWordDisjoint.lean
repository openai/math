import OAI.Computability.BorderVNP.FiniteSewnFieldUnique

/-! # Distinct physical cable and grouped-port input intervals at one real sewn site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew
open scoped Classical

variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    {ae ap be bp : ℕ} (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (v : N.Site)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "ord" => sourceOrder N oldEdge oldPort v
local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port v

local notation "wr" => wireInterval N lane B gw owner oldEdge oldPort edge port v
local notation "pr" => portStart N oldEdge oldPort v

omit [Fintype P] in
/-- The source enumeration distinguishes both ends at distinct hosts, one incidence for a
loop, and all attached grouped words. Translating their internal fragments to this same
old ordinal numbering gives pairwise disjoint descriptors over the entire site. -/
theorem port_words_separate (chunks : Attached N v → List Interval)
    (within : ∀ a q, q ∈ chunks a → q.oldStart+q.width ≤ width a.val)
    (separate : ∀ a, (chunks a).Pairwise Interval.Separate) :
    ((Finset.univ.toList.map wr) ++ (Finset.univ.toList.flatMap fun a => (chunks a).map (atOffset (pr a)))).Pairwise
      Interval.Separate := by
  have wireHit (e : Incident N v) (k : ℕ) (hit : (wr e).Hits k) :
      ∃ i : Fin (N.width e.val), (ord (.inl ⟨e,i⟩)).val = k := by
    let start := wireStart N oldEdge oldPort v e
    change start ≤ k ∧ k < start+N.width e.val at hit
    refine ⟨⟨k-start,by omega⟩,?_⟩
    rw [wireOrdinal]
    change start+(k-start)=k
    omega
  have attachedHit (a : Attached N v) (q : Interval) (hq : q ∈ chunks a) (k : ℕ)
      (hit : (atOffset (pr a) q).Hits k) :
      ∃ i : Fin (width a.val), (ord (.inr ⟨a,i⟩)).val = k := by
    let start := pr a
    change start+q.oldStart ≤ k ∧ k < start+q.oldStart+q.width at hit
    have cap := within a q hq
    refine ⟨⟨k-start,by omega⟩,?_⟩
    rw [portOrdinal]
    change start+(k-start)=k
    omega
  apply List.pairwise_append.mpr
  constructor
  · apply List.pairwise_map.mpr
    apply (Finset.univ.nodup_toList : (Finset.univ : Finset (Incident N v)).toList.Pairwise (·≠·)).imp
    intro a b ne k ha hb
    obtain ⟨i,ai⟩ := wireHit a k ha
    obtain ⟨j,bj⟩ := wireHit b k hb
    have eq := (ord).injective (Fin.ext (ai.trans bj.symm))
    exact ne (congrArg Sigma.fst (Sum.inl.inj eq))
  constructor
  · apply offsetBlocks_separate (fun a : Attached N v => width a.val) pr chunks within _ separate
    intro a b i j eq
    have ordEq := (portOrdinal N oldEdge oldPort v a i).trans (eq.trans (portOrdinal N oldEdge oldPort v b j).symm)
    exact congrArg Sigma.fst (Sum.inr.inj ((ord).injective (Fin.ext ordEq)))
  · intro a ha b hb k h₁ h₂
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨p,_,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨q,hm,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,eq₁⟩ := wireHit e k h₁
    obtain ⟨j,eq₂⟩ := attachedHit p q hm k h₂
    cases (ord).injective (Fin.ext (eq₁.trans eq₂.symm))

end Packing.SewnField

end BorderVNP
end Computability
end OAI
