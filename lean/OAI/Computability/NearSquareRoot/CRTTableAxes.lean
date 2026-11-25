import OAI.Computability.NearSquareRoot.CRTTableLayerIndex

/-! # Coordinates supplied by a CRT table at one depth

A local target coordinate is indexed by its node and its position in that
node's right child. These coordinates embed into the original padded box.
Their complement consists exactly of the left-child axes supplying the
complete control setting.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

/-- Nodes at this depth, in table order. -/
abbrev LevelNode (d n : ℕ) := Fin (CRTTree.level n (List.finRange d)).length

/-- One target field in a node's table. -/
abbrev TargetIndex (d n : ℕ) :=
  (j : LevelNode d n) × Fin (CRTTree.right ((CRTTree.level n (List.finRange d))[j.val])).length

/-- Original padded axis of the specified target field. -/
def targetAxis (d n : ℕ) (i : TargetIndex d n) : Fin d :=
  (CRTTree.right ((CRTTree.level n (List.finRange d))[i.1.val]))[i.2.val]

private theorem target_mem_node (d n : ℕ) (i : TargetIndex d n) :
    targetAxis d n i ∈ (CRTTree.level n (List.finRange d))[i.1.val] :=
  (List.drop_sublist _ _).subset (List.getElem_mem ..)

theorem targetAxis_injective (d n : ℕ) : Function.Injective (targetAxis d n) := by
  intro ⟨j,i⟩ ⟨k,l⟩ h
  let nodes := CRTTree.level n (List.finRange d)
  have hm (a : TargetIndex d n) : targetAxis d n a ∈ nodes[a.1.val] := target_mem_node d n a
  have hs := CRTTree.pairwise_disjoint_level n (List.nodup_finRange d)
  have hn {r s : LevelNode d n} (hr : r < s) : (nodes[r.val]).Disjoint nodes[s.val] :=
    List.pairwise_iff_getElem.mp hs _ _ r.isLt s.isLt hr
  have hjk : j = k := by
    rcases lt_trichotomy j k with lt|eq|gt
    · exact ((hn lt) (hm ⟨j,i⟩) (h.symm ▸ hm ⟨k,l⟩)).elim
    · exact eq
    · exact ((hn gt) (hm ⟨k,l⟩) (h ▸ hm ⟨j,i⟩)).elim
  subst k
  have hnodes : nodes.flatten.Nodup := by simpa only [nodes,CRTTree.flatten_level] using List.nodup_finRange d
  have hx := List.nodup_flatten.mp hnodes |>.1 nodes[j.val] (List.getElem_mem ..)
  have hr : (CRTTree.right nodes[j.val]).Nodup := hx.sublist (List.drop_sublist _ _)
  have hil : i = l := hr.injective_get h
  subst l
  rfl

theorem mem_targetAxis_range (d n : ℕ) (g : Fin d) :
    g ∈ Set.range (targetAxis d n) ↔
      g ∈ (CRTTree.level n (List.finRange d)).flatMap CRTTree.right := by
  constructor
  · rintro ⟨⟨j,i⟩,rfl⟩
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem (h := j.isLt), List.getElem_mem (h := i.isLt)⟩
  · intro hg
    obtain ⟨node,hnode,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hnode
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hg
    exact ⟨⟨j,i⟩,rfl⟩

/-- Padded coordinates held fixed by every lookup at this depth. -/
abbrev ExternalAxis (d n : ℕ) := {g : Fin d // g ∉ Set.range (targetAxis d n)}

theorem mem_controls_iff_external (d n : ℕ) (g : Fin d) :
    g ∈ CRTTree.controls n (List.finRange d) ↔ g ∉ Set.range (targetAxis d n) := by
  rw [mem_targetAxis_range]
  constructor
  · intro hc ht
    exact (CRTTree.controls_disjoint_targets n (List.nodup_finRange d)).1 hc ht
  · intro he
    have hf : g ∈ (CRTTree.level n (List.finRange d)).flatten := by simp
    obtain ⟨node,hn,hg⟩ := List.mem_flatten.mp hf
    have hparts : g ∈ CRTTree.left node ++ CRTTree.right node := by simpa using hg
    rcases List.mem_append.mp hparts with hl|hr
    · exact List.mem_flatMap.mpr ⟨node, hn, hl⟩
    · exact (he (List.mem_flatMap.mpr ⟨node, hn, hr⟩)).elim

theorem external_iff_mem_left (d n : ℕ) (g : Fin d) :
    g ∉ Set.range (targetAxis d n) ↔
      ∃ j : LevelNode d n, g ∈ CRTTree.left ((CRTTree.level n (List.finRange d))[j.val]) := by
  rw [← mem_controls_iff_external, CRTTree.controls, List.mem_flatMap]
  constructor
  · rintro ⟨node,hn,hg⟩
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hn
    exact ⟨j,hg⟩
  · rintro ⟨j,hg⟩
    exact ⟨_,List.getElem_mem ..,hg⟩

end CRTTable

end NearSquareRoot
end Computability
end OAI
