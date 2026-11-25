import OAI.Hierarchy.DescentPaddedSites
import OAI.Hierarchy.DescentColonyWinningSlabRead
import OAI.Hierarchy.DescentAffineColors

namespace OAI
/-! # Padding the inputs of both physical searches by empty public host slots -/

namespace Hierarchy.DescentColonies.Padded
open DescentGL DescentBinaryField DescentAffineColors
open scoped Classical BigOperators
noncomputable section
variable {k L H : ℕ} (le : L≤H)
def front : Fin L↪Fin H := Fin.castLEEmb le


def table (W : Fin L→Block k→ℕ) (s : Fin H) : Block k→ℕ :=
  if h:s.val<L then W ⟨s.val,h⟩ else fun _=>0

def neighbors (N : Fin L→List (Fin L)) (s : Fin H) : List (Fin H) :=
  if h:s.val<L then (N ⟨s.val,h⟩).map (front le) else []

theorem live_neighbors (N : Fin L→List (Fin L)) (v : Fin L) :
    neighbors le N (front le v)=(N v).map (front le) := by
  unfold neighbors
  split
  · rfl
  · rename_i outside
    exact False.elim (outside v.isLt)
theorem live_table (W : Fin L→Block k→ℕ) (v : Fin L) : table W (front le v)=W v := by
  unfold table
  split
  · rfl
  · rename_i outside
    exact False.elim (outside v.isLt)
theorem live_weight (W : Fin L→Block k→ℕ) (a μ : Bits k) (v : Fin L) (x : Block k) :
    multiplierLoad (table W) a μ (front le v) x=multiplierLoad W a μ v x := by
  unfold multiplierLoad
  split <;> simp only [live_table]
theorem ghost_weight (W : Fin L→Block k→ℕ) (a μ : Bits k) (v : Fin H) (ghost : ¬v.val<L) (x : Block k) :
    multiplierLoad (table W) a μ v x=0 := by unfold multiplierLoad;split <;> simp [table,ghost]

theorem uniform_score {G : Type} [Fintype G] (N : Fin L→List (Fin L)) (W : G→Fin L→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :
    uniformColonyScore (neighbors le N) (fun g=>table (W g)) D cap a μ=
      uniformColonyScore N W D cap a μ+Fintype.card G*(H-L) := by
  have one (g : G) := Scan.padding_score (front le) N (neighbors le N) (multiplierLoad (W g) a μ.val)
    (multiplierLoad (table (W g)) a μ.val) (live_neighbors le N) (live_weight le (W g) a μ.val)
    (fun v missing=>by
      have outside : ¬v.val<L := fun h=>missing ⟨⟨v.val,h⟩,Fin.ext rfl⟩
      exact ⟨by simp [neighbors,outside],ghost_weight (W g) a μ.val v outside⟩) D cap
  simp only [uniformColonyScore,one,Fintype.card_fin,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Nat.cast_id]

theorem same_multiplier {G : Type} [Fintype G] (N : Fin L→List (Fin L))
    (W : G→Fin L→Block k→ℕ) (D cap : ℕ) (a : Bits k) (seeds : List (Nonzero k)) :
    (scanMinimum (uniformColonyScore (neighbors le N) (fun g=>table (W g)) D cap a) seeds).1.map Prod.fst =
      (scanMinimum (uniformColonyScore N W D cap a) seeds).1.map Prod.fst := by
  have step := funext (uniform_score le N W D cap a)
  rw [step,minimum_shift]
  cases (scanMinimum (uniformColonyScore N W D cap a) seeds).1 <;> rfl

open WinningSlabs WinningSlabs.Selected
variable {G : ℕ}
def slots : Slot G L k↪Slot G H k :=
  (directory G L k).symm.toEmbedding.trans
    ((((Function.Embedding.refl (Fin G)).prodMap (front le)).prodMap
      (Function.Embedding.refl _)).trans (directory G H k).toEmbedding)

private theorem slots_at (g : Fin G) (v : Fin L) (name : Fin (keys k).length) :
    slots le (directory G L k ((g,v),name)) = directory G H k ((g,front le v),name) := by
  simp [slots, Function.Embedding.coe_prodMap]

theorem slab_score (N : Fin L→List (Fin L)) (W amt : Fin G→Fin L→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (j : Candidate k) :
    score (worldValue (winningRows (neighbors le N) (fun g=>table (W g)) D cap a μ)
      (winningAmounts (fun g=>table (amt g)) a μ)) j =
      score (worldValue (winningRows N W D cap a μ) (winningAmounts amt a μ)) j := by
  let big := worldValue (winningRows (neighbors le N) (fun g=>table (W g)) D cap a μ)
    (winningAmounts (fun g=>table (amt g)) a μ)
  let small := worldValue (winningRows N W D cap a μ) (winningAmounts amt a μ)
  have same (i : Slot G L k) (x : Block k) : big (slots le i) x=small i x := by
    obtain ⟨⟨⟨g,v⟩,nm⟩,rfl⟩ := (directory G L k).surjective i
    rw [slots_at]
    simp only [big,small,worldValue,Equiv.symm_apply_apply,
      filtered,member,winningRows,winningAmounts,Scan.leafDepth,
      Scan.padded_lookup (front le) N (neighbors le N) _ _ (live_neighbors le N)
        (live_weight le (W g) a μ.val),live_weight]
  have none (i : Slot G H k) (out : i∉Set.range (slots le)) (x : Block k) : big i x=0 := by
    obtain ⟨⟨⟨g,v⟩,nm⟩,rfl⟩ := (directory G H k).surjective i
    have fail : ¬v.val<L := by
      intro h
      apply out
      refine ⟨directory G L k ((g,⟨v.val,h⟩),nm),?_⟩
      have back : front le ⟨v.val,h⟩ = v := Fin.ext rfl
      rw [slots_at,back]
    simp only [big,worldValue,Equiv.symm_apply_apply,filtered,winningAmounts,ghost_weight _ _ _ _ fail,ite_self]
  let diff := fun A : Block k→ℕ=>difference (side A j true) (side A j false)
  have unused (v : Slot G H k) (_ : v∈Finset.univ) (miss : v∉Finset.univ.map (slots le)) : diff (big v)=0 := by
    have off : v∉Set.range (slots le) := fun ⟨u,eqn⟩=>miss (Finset.mem_map.mpr ⟨u,Finset.mem_univ _,eqn⟩)
    simp [diff,side,difference,none v off]
  change (∑v,diff (big v))=∑v,diff (small v)
  rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map (slots le))) unused,Finset.sum_map]
  exact Finset.sum_congr rfl (fun v _=>congrArg diff (funext (same v)))

end
end Hierarchy.DescentColonies.Padded

end OAI
