import OAI.Computability.BorderVNP.CubeISAOwnedSingleRowModel

/-! # Reading back the singleton banks after an owned row scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.SingleRowData

open Physical Physical.Owned RoutingISA VPVNP.BurstRAM DiagonalResidueRAM

open scoped Classical

variable {n d len w : ℕ} (D : SingleRowData n d len)

private abbrev Pair (n d : ℕ) := Label (n+1) d × Label (n+1) d

private def key {n d : ℕ} (p : Pair n d) :=
  (finFunctionFinEquiv p.1).val*d^(n+1)+(finFunctionFinEquiv p.2).val

private theorem key_val {n d : ℕ} (p : Pair n d) :
    key p = (finProdFinEquiv (finFunctionFinEquiv p.1,finFunctionFinEquiv p.2)).val := by
  dsimp [key,finProdFinEquiv]
  ac_rfl

private theorem key_inj {n d : ℕ} : Function.Injective (key (n := n) (d := d)) := by
  intro p q he
  rw [key_val,key_val] at he
  have h := finProdFinEquiv.injective (Fin.ext he)
  exact Prod.ext (finFunctionFinEquiv.injective (congrArg Prod.fst h))
    (finFunctionFinEquiv.injective (congrArg Prod.snd h))

/-- Native word address of a particular bit in the singleton bank of an ordered pair of labels. -/
def slotAddress (p : Label (n+1) d × Label (n+1) d) (j : Fin len) : ℕ :=
  singleBase D.bank (d^(n+1)) len (finFunctionFinEquiv p.1).val (finFunctionFinEquiv p.2).val+j.val

private theorem positions_len (t : Fin (singlePairTrials n d)) : (D.positions t).length = len := by
  simp [positions,singlePositions,bits]

private theorem one_slot (m : Memory w) (t : Fin (singlePairTrials n d)) (j : Fin len) :
    image (D.positions t) (D.address t) m (D.slotAddress (D.pair t) j) =
      wordBit w (D.value (D.pair t) j) := by
  let k : Fin (D.positions t).length := ⟨j.val,(D.positions_len t).symm ▸ j.isLt⟩
  apply image_at _ _ _ k
  by_cases same : D.left = D.right <;>
    simp [k,positions,singlePositions,bits,same,Position.value]

private theorem other_slot (t : Fin (singlePairTrials n d)) (p : Pair n d) (j : Fin len)
    (ne : D.pair t ≠ p) :
    D.slotAddress p j < D.address t ∨ D.address t+(D.positions t).length ≤ D.slotAddress p j := by
  rw [D.positions_len]
  change D.bank+key p*len+j.val < D.bank+key (D.pair t)*len ∨
    D.bank+key (D.pair t)*len+len ≤ D.bank+key p*len+j.val
  rcases lt_or_gt_of_ne (key_inj.ne ne) with h | h
  · have le := Nat.mul_le_mul_right len h
    rw [Nat.succ_mul] at le
    omega
  · have le := Nat.mul_le_mul_right len h
    rw [Nat.succ_mul] at le
    have := j.isLt
    omega

private def visited (k : ℕ) (p : Pair n d) : Prop :=
  ∃ t : Fin (singlePairTrials n d), t.val < k ∧ D.selected t ∧ D.pair t = p

private theorem visited_next (t : Fin (singlePairTrials n d)) (p : Pair n d) :
    D.visited (t.val+1) p ↔ D.visited t.val p ∨ (D.selected t ∧ D.pair t = p) := by
  constructor
  · rintro ⟨u,hu,hs,he⟩
    by_cases eq : u = t
    · subst u; exact Or.inr ⟨hs,he⟩
    · exact Or.inl ⟨u,by have := Fin.val_ne_of_ne eq; omega,hs,he⟩
  · rintro (⟨u,hu,hs,he⟩|⟨hs,he⟩)
    · exact ⟨u,by omega,hs,he⟩
    · exact ⟨t,Nat.lt_succ_self _,hs,he⟩

private theorem prefix_slot (m : Memory w) (k : ℕ) (hk : k ≤ singlePairTrials n d)
    (p : Pair n d) (j : Fin len) :
    (D.before m k).2 (D.slotAddress p j) = if D.visited k p then wordBit w (D.value p j)
      else m (D.slotAddress p j) := by
  classical
  induction k with
  | zero => simp [before,visited]
  | succ k ih =>
    let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
    change (D.before m (t.val+1)).2 _ = if D.visited (t.val+1) p then _ else _
    rw [D.visited_next]
    by_cases selected : D.selected t
    · rw [D.before_visit m t selected]
      by_cases same : D.pair t = p
      · subst p
        simpa only [selected,and_self,eq_self,true_and,or_true,ite_true] using D.one_slot (D.before m k).2 t j
      · dsimp only
        rw [image_outside _ _ _ (D.other_slot t p j same)]
        simpa only [same,and_false,or_false] using ih (by omega)
    · rw [D.before_skip m t selected]
      simpa only [selected,false_and,or_false] using ih (by omega)

/-- Every actual singleton whose two grouping symbols agree with this ordered row
has its prescribed word in the final bank, whether routed or locally guessed. -/
theorem final_slot {blocks width : ℕ} (D : SingleRowData n d (blocks*width)) (m : Memory w)
    (z : SingleSlot n d blocks width) (left : z.1.val.1 D.axis = D.left) (right : z.1.val.2 D.axis = D.right) :
    (D.before m (singlePairTrials n d)).2 (D.slotAddress z.1.val z.2) = wordBit w (D.value z.1.val z.2) := by
  let e := singleOrderedPairs D.axis D.left D.right
  let p : {p : Pair n d // p.1 D.axis = D.left ∧ p.2 D.axis = D.right} := ⟨z.1.val,left,right⟩
  let t := e.symm p
  have he : D.pair t = z.1.val := congrArg Subtype.val (e.apply_symm_apply p)
  have yes : D.selected t := by
    change ¬∀ i, (D.pair t).1 i ≠ (D.pair t).2 i
    rw [he]
    exact z.1.property
  rw [D.prefix_slot m _ le_rfl,ite_eq_left ⟨t,t.isLt,yes,he⟩]

/-- Another oriented grouping row leaves this singleton word exactly as it was. -/
theorem final_unrelated (m : Memory w) (p : Label (n+1) d × Label (n+1) d) (j : Fin len)
    (other : ¬(p.1 D.axis = D.left ∧ p.2 D.axis = D.right)) :
    (D.before m (singlePairTrials n d)).2 (D.slotAddress p j) = m (D.slotAddress p j) := by
  rw [D.prefix_slot m _ le_rfl,ite_eq_right]
  rintro ⟨t,_,_,rfl⟩
  exact other ((singleOrderedPairs D.axis D.left D.right t).property)

/-- Any already correct word survives another row scan, including a rescan of the same row. -/
theorem final_preserves_correct (m : Memory w) (p : Label (n+1) d × Label (n+1) d) (j : Fin len)
    (correct : m (D.slotAddress p j) = wordBit w (D.value p j)) :
    (D.before m (singlePairTrials n d)).2 (D.slotAddress p j) = wordBit w (D.value p j) := by
  rw [D.prefix_slot m _ le_rfl,correct]
  simp

/-- Every address outside the global ordered-pair singleton reservation retains
its original word, throughout the row and at the final memory. -/
theorem final_outside (m : Memory w) (k a : ℕ)
    (outside : a < D.bank ∨ D.bank+d^(n+1)*d^(n+1)*len ≤ a) : (D.before m k).2 a = m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < singlePairTrials n d
    · let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
      by_cases yes : D.selected t
      · rw [D.before_visit m t yes]
        apply (image_outside _ _ _ ?_).trans ih
        rw [D.positions_len]
        change a < D.bank + key (D.pair t)*len ∨ D.bank + key (D.pair t)*len + len ≤ a
        have hk' : key (D.pair t) < d^(n+1)*d^(n+1) := by
          rw [key_val]
          exact Fin.isLt _
        have lim := Nat.mul_le_mul_right len hk'
        rw [Nat.succ_mul] at lim
        omega
      · rw [D.before_skip m t yes]; exact ih
    · simpa only [before,hk,dite_false] using ih

end Cube.Scatter.SingleRowData

end BorderVNP
end Computability
end OAI
