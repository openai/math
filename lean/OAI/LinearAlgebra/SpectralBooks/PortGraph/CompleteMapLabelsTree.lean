import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsTreeDistance
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsTreeChildren

/-! # Local verification of subtree sums and preorder names

At a parent, the one-based port reported by each neighbor identifies the child
slots. A prefix sum over these slots gives the preorder offset for each child.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize
open scoped Classical BigOperators

variable {N : ℕ}

/-- Read the three fields determining the named spanning tree. -/
def treeRecord {V : Type*} (b : V → BaseAlphabet N) : TreeNameRecord V where
  distance v := vertexVal (b v) .distance
  size v := vertexVal (b v) .subtreeSize
  name v := vertexVal (b v) .preorderName

def childSum (z : PortView (BaseAlphabet N) 1) (keep : ℕ → Bool) (f : VertexField) : ℕ :=
  ∑ i : Fin 4, (childAt z i).elim 0 (fun a => if keep i.val then vertexVal a f else 0)

def subtreeTest (f : VertexField) (weight : ℕ) (z : PortView (BaseAlphabet N) 1) : Prop :=
  vertexVal z.1 f = weight + childSum z (fun _ => true) f

def namesTest (z : PortView (BaseAlphabet N) 1) : Prop :=
  (z.1.1 = true → vertexVal z.1 .preorderName = 1) ∧
  ∀ i a, childAt z i = some a →
    vertexVal a .preorderName = vertexVal z.1 .preorderName + 1 +
      childSum z (fun j => decide (j < i.val)) .subtreeSize

def treeTest (z : PortView (BaseAlphabet N) 1) : Prop :=
  distanceParentTest z ∧ subtreeTest .subtreeSize 1 z ∧ namesTest z ∧
    (z.1.1 = true → vertexVal z.1 .subtreeSize ≤ N)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
  (b : V → BaseAlphabet N)
  (hd : DistanceChecks (underlying M.graph.tail M.graph.head) M.root (treeRecord b).distance)
  (hp : ∀ v, vertexVal (b v) .parentPort = parentCode M _ hd v)

local notation "P" => canonicalParent M.graph M.slotNat M.slotNat_injective hd
local notation "S" => canonicalSiblingSlot M.graph M.slotNat M.slotNat_injective hd

private theorem childSlot_lt {w : V} (hw : w ≠ M.root) : S w < 4 := by
  rw [canonicalSiblingSlot_eq _ _ _ hd _ hw]
  exact (M.slots _ _).isLt

include hp in
private theorem childSum_actual (v : V) (keep : ℕ → Bool) (f : VertexField) :
    childSum (PortView.actual M.slots b 1 v) keep f =
      ∑ w ∈ (treeChildren M.root P v).filter (fun w => keep (S w)), vertexVal (b w) f := by
  let kids := treeChildren M.root P v
  let value (w : V) := vertexVal (b w) f
  let z := PortView.actual M.slots b 1 v
  have oneSlot (i : Fin 4) : (childAt z i).elim 0 (fun a => if keep i.val then vertexVal a f else 0) =
      ∑ w ∈ kids, if S w = i.val then (if keep i.val then value w else 0) else 0 := by
    cases hc : childAt z i with
    | none =>
      symm
      apply Finset.sum_eq_zero
      intro w hw
      have hne : S w ≠ i.val := fun eq => by
        have := (childAt_actual_iff M b hd hp v i (b w)).mpr ⟨w,hw,eq,rfl⟩
        rw [hc] at this
        contradiction
      simp [hne]
    | some a =>
      obtain ⟨w,hw,hs,rfl⟩ := (childAt_actual_iff M b hd hp v i a).mp hc
      change S w = i.val at hs
      change w ∈ kids at hw
      rw [Finset.sum_eq_single w]
      · rw [ite_eq_left hs]
        rfl
      · intro u hu hne
        have hnu : S u ≠ i.val := by
          intro he
          obtain ⟨hu',hpu⟩ := (Finset.mem_filter.mp hu).2
          obtain ⟨hw',hpw⟩ := (Finset.mem_filter.mp hw).2
          exact hne (canonicalSiblingSlot_injective _ _ _ hd hu' hw' (hpu.trans hpw.symm) (he.trans hs.symm))
        simp [hnu]
      · exact fun h => False.elim (h hw)
  change (∑ i : Fin 4, (childAt z i).elim 0 (fun a => if keep i.val then vertexVal a f else 0)) = _
  simp_rw [oneSlot]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  let i : Fin 4 := ⟨S w,childSlot_lt M b hd (Finset.mem_filter.mp hw).2.1⟩
  rw [Finset.sum_eq_single i]
  · simp [i,value]
  · intro j _ hj
    have hn : S w ≠ j.val := fun h => hj (Fin.ext h.symm)
    simp [hn]
  · simp

include hp in
theorem subtreeTest_iff (f : VertexField) (weight : V → ℕ) :
    (∀ v, subtreeTest f (weight v) (PortView.actual M.slots b 1 v)) ↔
      SubtreeTotals M.root P weight (fun v => vertexVal (b v) f) := by
  simp only [subtreeTest, childSum_actual M b hd hp, SubtreeTotals]
  simp [PortView.actual]

include hp in
private theorem namesTest_iff (hroot : ∀ v, (b v).1 = (M.typeAt v).root) :
    (∀ v, namesTest (PortView.actual M.slots b 1 v)) ↔
      PreorderNames M.root P S (treeRecord b).size (treeRecord b).name := by
  have hr (v : V) : (b v).1 = true ↔ v = M.root := by
    rw [hroot]
    exact decide_eq_true_iff
  have he (v : V) (i : Fin 4) :
      childSum (PortView.actual M.slots b 1 v) (fun j => decide (j < i.val)) .subtreeSize =
      ∑ w ∈ (treeChildren M.root P v).filter (fun w => S w < i.val), (treeRecord b).size w := by
    rw [childSum_actual M b hd hp]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext w
    simp
  constructor
  · intro h
    refine ⟨(h _).1 ((hr _).mpr rfl),fun w hw => ?_⟩
    let i : Fin 4 := ⟨S w,childSlot_lt M b hd hw⟩
    have hc := (childAt_actual_iff M b hd hp (P w) i (b w)).mpr
      ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,rfl⟩,rfl,rfl⟩
    have hn := (h _).2 i _ hc
    rw [he] at hn
    exact hn
  · intro h v
    refine ⟨fun hv => ?_,fun i a hc => ?_⟩
    · obtain rfl := (hr _).mp hv
      exact h.1
    · obtain ⟨w,hw,hs,rfl⟩ := (childAt_actual_iff M b hd hp v i a).mp hc
      obtain ⟨hn,rfl⟩ := (Finset.mem_filter.mp hw).2
      rw [he,← hs]
      exact h.2 w hn

omit hd hp in
theorem treeTest_iff (hroot : ∀ v, (b v).1 = (M.typeAt v).root) :
    (∀ v, treeTest (PortView.actual M.slots b 1 v)) ↔
      ∃ ht : M.NameChecks (treeRecord b),
        (∀ v, vertexVal (b v) .parentPort = parentCode M _ ht.distances v) ∧
        (treeRecord b).size M.root ≤ N := by
  constructor
  · intro h
    obtain ⟨hd,hp⟩ := (distanceParentTest_iff M b hroot).mp (fun v => (h v).1)
    have hs := (subtreeTest_iff M b hd hp .subtreeSize (fun _ => 1)).mp (fun v => (h v).2.1)
    have hn := (namesTest_iff M b hd hp hroot).mp (fun v => (h v).2.2.1)
    have hr : (b M.root).1 = true := by simp [hroot,RootedMap.typeAt]
    exact ⟨⟨hd,hs,hn⟩,hp,(h M.root).2.2.2 hr⟩
  · rintro ⟨ht,hp,hcap⟩
    have hdist := (distanceParentTest_iff M b hroot).mpr ⟨ht.distances,hp⟩
    have hs := (subtreeTest_iff M b ht.distances hp .subtreeSize (fun _ => 1)).mpr ht.sizes
    have hn := (namesTest_iff M b ht.distances hp hroot).mpr ht.names
    refine fun v => ⟨hdist v,hs v,hn v,fun hv => ?_⟩
    change (b v).1 = true at hv
    obtain rfl : v = M.root := by simpa [hroot,RootedMap.typeAt] using hv
    exact hcap

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
