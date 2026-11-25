import OAI.Hierarchy.DescentRotorReset

namespace OAI
/-! # Contiguous group assignment for every bundle of an integer routing matrix -/

namespace Hierarchy.DescentRotor
open Finset
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def groups (w m : ℕ) := ⌈(m : ℝ)/w⌉₊

abbrev Packet (w : ℕ) (m : V → V → ℕ) := Σ i : V, Σ j : V, Fin (groups w (m i j))

private theorem full {w m : ℕ} (hw : 0 < w) : m ≤ groups w m*w := by
  have h := (div_le_iff₀ (by exact_mod_cast hw : (0:ℝ) < w)).mp (Nat.le_ceil ((m:ℝ)/w))
  exact_mod_cast h

private def which {w : ℕ} (hw : 0 < w) {m : V → V → ℕ} (i j : V) (b : Fin (m i j)) : Packet w m :=
  ⟨i,j,⟨b.val/w,(Nat.div_lt_iff_lt_mul hw).2 (b.isLt.trans_le (full hw))⟩⟩

/-- Each input bit of each integer entry is placed in a concrete rotor layer and one of
its w input row bits. The output is forced to the target named by that matrix entry.
Different bits at one input never claim the same physical layer and row bit. -/
theorem pack_matrix (m : V → V → ℕ) {w : ℕ} (hw : 0 < w) (L : ℕ)
    (row : ∀ i, (∑ j, groups w (m i j)) ≤ L)
    (col : ∀ j, (∑ i, groups w (m i j)) ≤ L) :
    ∃ choose : ∀ i j, Fin (m i j) → Fin (2*L+1) × Fin w,
    ∃ σ : Fin (2*L+1) → Equiv.Perm V,
      (∀ i j b, σ (choose i j b).1 i=j) ∧
      ∀ i j k (b : Fin (m i j)) (c : Fin (m i k)), choose i j b=choose i k c →
        j=k ∧ b.val=c.val := by
  classical
  let source (p : Packet w m) := p.1
  let target (p : Packet w m) := p.2.1
  have rows (i : V) : (Finset.univ.filter fun p => source p=i).card ≤ L := by
    rw [Finset.card_filter,Fintype.sum_sigma]
    change (∑ v : V, ∑ u : Σ j : V, Fin (groups w (m v j)), if v=i then 1 else 0) ≤ L
    conv_lhs =>
      enter [2,v]
      rw [Finset.sum_ite_irrel]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_one,nsmul_zero,Fintype.card_sigma,Fintype.card_fin]
    simpa using row i
  have cols (j : V) : (Finset.univ.filter fun p => target p=j).card ≤ L := by
    rw [Finset.card_filter,Fintype.sum_sigma]
    apply le_trans _ (col j)
    apply Finset.sum_le_sum
    intro v _
    rw [Fintype.sum_sigma]
    change (∑ t : V, ∑ _ : Fin (groups w (m v t)), if t=j then 1 else 0) ≤ groups w (m v j)
    simp only [Finset.sum_ite_irrel,Finset.sum_const,Finset.card_univ,nsmul_one,nsmul_zero,Fintype.card_fin]
    simp
  obtain ⟨color,σ,go,unique⟩ := permutation_layers source target L rows cols
  let choose (i j : V) (b : Fin (m i j)) := (color (which hw i j b), (⟨b.val%w,Nat.mod_lt _ hw⟩ : Fin w))
  refine ⟨choose,σ,fun i j b => go (which hw i j b),?_⟩
  intro i j k b c same
  have p := unique (which hw i j b) (which hw i k c) (congrArg Prod.fst same) rfl
  refine ⟨congrArg target p,?_⟩
  have q := congrArg (fun t : Packet w m => t.2.2.val) p
  have r := congrArg (fun t : Fin (2*L+1) × Fin w => t.2.val) same
  change b.val/w=c.val/w at q
  change b.val%w=c.val%w at r
  calc b.val = b.val%w+w*(b.val/w) := (Nat.mod_add_div _ _).symm
       _ = c.val := by rw [q,r,Nat.mod_add_div]

omit [DecidableEq V] in
/-- The actual ceiling counts satisfy the row bound used in the per-layer cost calculation. -/
theorem row_reset_bound (bundles : V → ℕ) {w : ℕ} (hw : 0 < w) {F B u : ℝ}
    (positive : 0<(Fintype.card V : ℝ)) (hu : 0 < u) (huB : u ≤ B)
    (scale : (Fintype.card V:ℝ)^2*w ≤ F)
    (load : ∑ v, (bundles v:ℝ)≤9*F*B/(Fintype.card V*u)) :
    ∑ v, (groups w (bundles v):ℝ) ≤ 10*F*B/(Fintype.card V*w*u) := by
  let Y : ℝ := Fintype.card V
  have hY : 0 < Y := positive
  have hW : (0:ℝ) < w := by exact_mod_cast hw
  have main := (le_div_iff₀ (mul_pos hY hu)).mp load
  have pos := mul_pos (mul_pos hY hW) hu
  have cheap : Y^2*w*u ≤ F*B := by
    calc
      _ ≤ F*u := mul_le_mul_of_nonneg_right scale hu.le
      _ ≤ F*B := mul_le_mul_of_nonneg_left huB (le_trans (by positivity) scale)
  apply (packed_sum_le bundles hw).trans
  apply (le_div_iff₀ pos).2
  have div := div_mul_cancel₀ (∑ v, (bundles v:ℝ)) hW.ne'
  change ((∑ v, (bundles v:ℝ))/w+Y)*(Y*w*u) ≤ 10*F*B
  change (∑ v, (bundles v:ℝ))*(Y*u)≤9*F*B at main
  nlinarith only [main,cheap,congrArg (fun q : ℝ => q*(Y*u)) div]

end
end Hierarchy.DescentRotor

end OAI
