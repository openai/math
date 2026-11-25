import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Radius-one distance and parent-port tests -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize

variable {N : ℕ}

/-- An occupied departure slot leads to a closer reported distance. -/
def closerSlot (z : PortView (BaseAlphabet N) 1) (i : Fin 4) : Prop :=
  ∃ j a, z.2 i = some (j,a) ∧ vertexVal a .distance < vertexVal z.1 .distance

def distanceParentTest (z : PortView (BaseAlphabet N) 1) : Prop :=
  (vertexVal z.1 .distance = 0 ↔ z.1.1 = true) ∧
  (∀ i j a, z.2 i = some (j,a) → vertexVal z.1 .distance ≤ vertexVal a .distance + 1) ∧
  (if z.1.1 then vertexVal z.1 .parentPort = 0 else
    ∃ i, closerSlot z i ∧ vertexVal z.1 .parentPort = i.val + 1 ∧
      ∀ k, closerSlot z k → i ≤ k)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (M : RootedMap V E) (b : V → BaseAlphabet N)

theorem treeView_port {v : V} (p : M.graph.Port v) :
    (PortView.actual M.slots b 1 v).2 (M.slots v p) =
      some (M.slots _ (reversePort M.graph p), b (otherEnd M.graph p)) := by
  simp only [PortView.actual, portStep_port, Option.map_some]
  rfl

theorem treeView_slot {v : V} {i j : Fin 4} {a : BaseAlphabet N}
    (h : (PortView.actual M.slots b 1 v).2 i = some (j,a)) :
    ∃ p : M.graph.Port v, M.slots v p = i ∧ M.slots _ (reversePort M.graph p) = j ∧
      b (otherEnd M.graph p) = a := by
  classical
  by_cases hi : ∃ p : M.graph.Port v, M.slots v p = i
  · obtain ⟨p,rfl⟩ := hi
    rw [treeView_port] at h
    exact ⟨p,rfl, congrArg Prod.fst (Option.some.inj h), congrArg Prod.snd (Option.some.inj h)⟩
  · simp [PortView.actual, portStep_missing _ _ _ _ hi] at h

private theorem closerSlot_port {v : V} (p : M.graph.Port v) :
    closerSlot (PortView.actual M.slots b 1 v) (M.slots v p) ↔
      vertexVal (b (otherEnd M.graph p)) .distance < vertexVal (b v) .distance := by
  constructor
  · rintro ⟨j,a,h,ha⟩
    rw [treeView_port] at h
    obtain rfl : b (otherEnd M.graph p) = a := congrArg Prod.snd (Option.some.inj h)
    exact ha
  · exact fun h => ⟨_,_,treeView_port M b p,h⟩

private theorem port_of_adjacency {v w : V} (h : (underlying M.graph.tail M.graph.head).Adj v w) :
    ∃ p : M.graph.Port v, otherEnd M.graph p = w := by
  obtain ⟨_, e, ⟨ht, hh⟩ | ⟨hh, ht⟩⟩ := h
  · exact ⟨⟨(e,false),ht⟩,hh⟩
  · exact ⟨⟨(e,true),ht⟩,hh⟩

private theorem adjacency_of_port {v : V} (p : M.graph.Port v) (hne : v ≠ otherEnd M.graph p) :
    (underlying M.graph.tail M.graph.head).Adj v (otherEnd M.graph p) := by
  obtain ⟨⟨e, s⟩, rfl⟩ := p
  exact ⟨hne,e,by cases s <;> simp [otherEnd, PortGraph.vertex]⟩

@[reducible] def parentCode (d : V → ℕ)
    (hd : DistanceChecks (underlying M.graph.tail M.graph.head) M.root d) (v : V) : ℕ :=
  if h : v = M.root then 0 else
    M.slotNat v (canonicalParentPort M.graph M.slotNat M.slotNat_injective hd v h) + 1

theorem distanceParentTest_iff (hroot : ∀ v, (b v).1 = (M.typeAt v).root) :
    (∀ v, distanceParentTest (PortView.actual M.slots b 1 v)) ↔
      ∃ hd : DistanceChecks (underlying M.graph.tail M.graph.head) M.root
        (fun v => vertexVal (b v) .distance),
        ∀ v, vertexVal (b v) .parentPort = parentCode M _ hd v := by
  classical
  have hr (v : V) : (b v).1 = decide (v = M.root) := hroot v
  let d := fun v => vertexVal (b v) .distance
  constructor
  · intro h
    have zero (v : V) : d v = 0 ↔ v = M.root := by
      simpa [d,hr] using (show vertexVal (b v) .distance = 0 ↔ (b v).1 = true from (h v).1)
    have step {v w : V} (adj : (underlying M.graph.tail M.graph.head).Adj v w) : d v ≤ d w + 1 := by
      obtain ⟨p,rfl⟩ := port_of_adjacency M adj
      exact (h v).2.1 _ _ _ (treeView_port M b p)
    have select (v : V) (hv : v ≠ M.root) : ∃ p : M.graph.Port v,
        IsParentPort M.graph M.slotNat d v p ∧ vertexVal (b v) .parentPort = M.slotNat v p + 1 := by
      have hc := (h v).2.2
      change (if (b v).1 then _ else _) at hc
      rw [hr,decide_eq_false hv] at hc
      obtain ⟨i,⟨j,a,hij,hlt⟩, hcode, hmin⟩ := hc
      obtain ⟨p,rfl,-,rfl⟩ := treeView_slot M b hij
      exact ⟨p,⟨hlt,fun q hq => hmin _ ((closerSlot_port M b q).mpr hq)⟩, hcode⟩
    have hd : DistanceChecks (underlying M.graph.tail M.graph.head) M.root d :=
      ⟨zero,fun ⦃_ _⦄ h => step h,fun v hv => by
        obtain ⟨p,⟨hlt,-⟩,-⟩ := select v hv
        exact ⟨_,adjacency_of_port M p (fun e => (ne_of_lt hlt) (congrArg d e.symm)),hlt⟩⟩
    refine ⟨hd, fun v => ?_⟩
    by_cases hv : v = M.root
    · have hc := (h v).2.2
      change (if (b v).1 then _ else _) at hc
      simpa [parentCode,hr,hv,PortView.actual] using hc
    · obtain ⟨p,hp,hc⟩ := select v hv
      rw [eq_canonicalParentPort _ _ _ hd _ hv p hp] at hc
      simpa [parentCode,hv] using hc
  · rintro ⟨hd,hp⟩ v
    refine ⟨?_,?_,?_⟩
    · change vertexVal (b v) .distance = 0 ↔ (b v).1 = true
      simpa [hr] using hd.zero v
    · intro i j a hij
      obtain ⟨p,-,-,rfl⟩ := treeView_slot M b hij
      by_cases he : v = otherEnd M.graph p
      · change d v ≤ d (otherEnd M.graph p) + 1
        rw [← he]
        omega
      · exact hd.step (adjacency_of_port M p he)
    · change (if (b v).1 then _ else _)
      rw [hr]
      split
      · rename_i hv
        have he : v = M.root := of_decide_eq_true hv
        simpa [parentCode,he,PortView.actual] using hp v
      · rename_i hv
        have he : v ≠ M.root := by simpa using hv
        let p := canonicalParentPort M.graph M.slotNat M.slotNat_injective hd v he
        have hs := canonicalParentPort_spec M.graph M.slotNat M.slotNat_injective hd v he
        refine ⟨M.slots v p,(closerSlot_port M b p).mpr hs.1,?_,?_⟩
        · change vertexVal (b v) .parentPort = M.slotNat v p + 1
          simpa [parentCode,he,p] using hp v
        · rintro k ⟨j,a,hka,hlt⟩
          obtain ⟨q,rfl,-,rfl⟩ := treeView_slot M b hka
          exact hs.2 q hlt

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
