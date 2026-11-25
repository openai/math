import OAI.Computability.NearSquareRoot.InterchangeStageLift

/-!
# Moving occupied reserve coordinates in a complete tape address

The physical reserve pivots exchange the early difference fields with a
matched set of late reserve fields.  Reading the active query after this
exchange is a reshuffle of the original active coordinates. Undoing the
pivots restores the original contents of every displaced late field.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeStageLift

open IntegerMultiplication.Port NearSquareRoot.InterchangeSlots

variable {a c e m p : ℕ} {R : Type}

/-- The coordinate of the original `a+2` vector occupying a given position
of the rectangle's `c+(2+e)` vector. -/
def shuffle (hce : c+e=a) : Fin (c+(2+e)) ≃ Fin (a+2) where
  toFun i := ⟨if i.val < c then i.val else if i.val < c+2 then a+(i.val-c) else i.val-2,
    by split_ifs <;> omega⟩
  invFun k := ⟨if k.val < c then k.val else if k.val < a then k.val+2 else c+(k.val-a),
    by split_ifs <;> omega⟩
  left_inv i := by apply Fin.ext; dsimp only; split_ifs <;> omega
  right_inv k := by apply Fin.ext; dsimp only; split_ifs <;> omega

theorem shuffle_first (hce : c+e=a) (i : Fin c) :
    shuffle hce (Fin.castAdd (2+e) i) = Fin.castAdd 2 (Fin.cast hce (Fin.castAdd e i)) := by
  apply Fin.ext
  simp [shuffle,i.isLt]

theorem shuffle_middle (hce : c+e=a) (k : Fin 2) :
    shuffle hce (Fin.natAdd c (Fin.castAdd e k)) = Fin.natAdd a k := by
  apply Fin.ext
  simp [shuffle,show c+k.val < c+2 by omega]

theorem shuffle_last (hce : c+e=a) (l : Fin e) :
    shuffle hce (Fin.natAdd c (Fin.natAdd 2 l)) = Fin.castAdd 2 (Fin.cast hce (Fin.natAdd c l)) := by
  apply Fin.ext
  simp [shuffle,show ¬c+(2+l.val) < c+2 by omega]
  omega

/-- Linear coordinate reindexing, available in every residue ring. -/
def shuffleLinear (K R : Type) [Semiring K] [AddCommMonoid R] [Module K R] (hce : c+e=a) :
    (Fin (a+2) → R) ≃ₗ[K] (Fin (c+(2+e)) → R) where
  toFun z := z ∘ shuffle hce
  invFun z := z ∘ (shuffle hce).symm
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Permute physical slots; this map also specifies where each displaced
late spare is temporarily kept. -/
private def switchSpot (hce : c+e=a) (s : Spot (Fin (a+m+a))) : Spot (Fin (a+m+a)) :=
  match s with
  | (false,k) => if lo : c ≤ k.val then if hi : k.val < a then
      (true, lateReserve hce ⟨k.val-c, by omega⟩) else (false,k) else (false,k)
  | (true,k) => if lo : a+m ≤ k.val then if hi : k.val < a+m+e then
      (false, earlyReserve hce ⟨k.val-(a+m), by omega⟩) else (true,k) else (true,k)

private theorem switch_early (hce : c+e=a) (i : Fin e) :
    switchSpot (m:=m) hce (false,earlyReserve hce i) = (true,lateReserve hce i) := by
  simp [switchSpot,earlyReserve,lateReserve,show c + i.val < a by omega]

private theorem switch_late (hce : c+e=a) (i : Fin e) :
    switchSpot (m:=m) hce (true,lateReserve hce i) = (false,earlyReserve hce i) := by
  simp [switchSpot,earlyReserve,lateReserve]

private theorem switch_other (hce : c+e=a) (s : Spot (Fin (a+m+a)))
    (h : ∀ i : Fin e, s ≠ (false,earlyReserve hce i) ∧ s ≠ (true,lateReserve hce i)) :
    switchSpot hce s = s := by
  rcases s with ⟨_ | _,k⟩ <;> dsimp only [switchSpot]
  · split_ifs with lo hi
    · exact False.elim ((h ⟨k.val-c,by omega⟩).1 (by congr 1; apply Fin.ext; dsimp [earlyReserve]; omega))
    all_goals rfl
  · split_ifs with lo hi
    · exact False.elim ((h ⟨k.val-(a+m),by omega⟩).2 (by congr 1; apply Fin.ext; dsimp [lateReserve]; omega))
    all_goals rfl

private theorem switch_involutive (hce : c+e=a) : Function.Involutive (switchSpot (m:=m) hce) := by
  intro s
  by_cases h : ∃ i : Fin e, s = (false, earlyReserve hce i)
  · obtain ⟨i,rfl⟩ := h
    rw [switch_early,switch_late]
  by_cases h' : ∃ i : Fin e, s = (true, lateReserve hce i)
  · obtain ⟨i,rfl⟩ := h'
    rw [switch_late,switch_early]
  have hs := switch_other hce s (fun i => ⟨fun hi => h ⟨i,hi⟩,fun hi => h' ⟨i,hi⟩⟩)
  rw [hs,hs]

private def moveSlots (hce : c+e=a) (x : Duplex (Fin (a+m+a)) R) : Duplex (Fin (a+m+a)) R :=
  (fun k => hear x (switchSpot hce (false,k)), fun k => hear x (switchSpot hce (true,k)))

private theorem hear_moveSlots (hce : c+e=a) (x : Duplex (Fin (a+m+a)) R) (s) :
    hear (moveSlots hce x) s = hear x (switchSpot hce s) := by
  rcases s with ⟨_ | _,k⟩ <;> rfl

/-- Action of the occupied-reserve exchange on full addresses over arbitrary
alphabets. -/
def reserveShift (hce : c+e=a) : Equiv.Perm (Duplex (Fin (a+m+a)) R) :=
  Function.Involutive.toPerm (moveSlots hce) (fun x => by
    apply hear_all
    intro s
    rw [hear_moveSlots,hear_moveSlots,switch_involutive hce s])

/-- The exchange reads both members of each pair and preserves every other slot. -/
theorem reserveShift_effect (hce : c+e=a) (x : Duplex (Fin (a+m+a)) R) :
    let y := reserveShift hce x
    (∀ i : Fin e, hear y (false,earlyReserve hce i) = hear x (true,lateReserve hce i) ∧
      hear y (true,lateReserve hce i) = hear x (false,earlyReserve hce i)) ∧
    ∀ u, (∀ i : Fin e, u ≠ (false,earlyReserve hce i) ∧ u ≠ (true,lateReserve hce i)) →
      hear y u = hear x u := by
  change (∀ i, hear (moveSlots hce x) _ = _ ∧ hear (moveSlots hce x) _ = _) ∧
    ∀ u, _ → hear (moveSlots hce x) u = _
  constructor
  · intro i
    rw [hear_moveSlots,hear_moveSlots,switch_early,switch_late]
    exact ⟨rfl,rfl⟩
  · intro u hu
    rw [hear_moveSlots,switch_other hce u hu]

theorem reservePivots_eq_shift (hce : c+e=a) (f : ℕ)
    (x : Duplex (Fin (a+m+a)) (Tower p f)) :
    (reservePivots hce).foldl (Lag.fire f) x = reserveShift hce x := by
  obtain ⟨swap,fix⟩ := reservePivots_effect hce f x
  apply hear_all
  intro s
  change _ = hear (moveSlots hce x) s
  rw [hear_moveSlots]
  by_cases h : ∃ i : Fin e, s = (false,earlyReserve hce i)
  · obtain ⟨i,rfl⟩ := h
    rw [switch_early]
    exact (swap i).1
  by_cases h' : ∃ i : Fin e, s = (true,lateReserve hce i)
  · obtain ⟨i,rfl⟩ := h'
    rw [switch_late]
    exact (swap i).2
  have hs : ∀ i : Fin e, s ≠ (false,earlyReserve hce i) ∧ s ≠ (true,lateReserve hce i) :=
    fun i => ⟨fun hi => h ⟨i,hi⟩,fun hi => h' ⟨i,hi⟩⟩
  rw [switch_other hce s hs]
  exact fix s hs

/-- Every active physical slot of the rectangle has its specified
original predecessor.  This identity also covers both main fields. -/
private theorem switch_active (hce : c+e=a) (j : Fin m) (i : Fin (c+(2+e))) :
    switchSpot hce (active hce j i) = querySlots a j (shuffle hce i) := by
  by_cases hc : i.val < c
  · have ha : i.val < a := by omega
    simp [shuffle,active,querySlots,switchSpot,hc,ha]
  by_cases h₁ : i.val = c
  · rw [show i = ⟨c, (by omega : c<c+(2+e))⟩ from Fin.ext h₁]
    rw [active_first]
    simp [shuffle, querySlots,active,switchSpot,mainRank]
  by_cases h₂ : i.val = c+1
  · rw [show i = ⟨c+1, (by omega : c+1<c+(2+e))⟩ from Fin.ext h₂]
    rw [active_second]
    simp [shuffle, querySlots,active,switchSpot,mainRank,
      show ¬a+m ≤ a+j.val by omega]
  let k : Fin e := ⟨i.val-(c+2), by omega⟩
  have hk : i = ⟨c+2+k.val, by dsimp [k]; omega⟩ := Fin.ext (by dsimp [k]; omega)
  rw [hk, active_difference, switch_late]
  have hsh : shuffle hce ⟨c+2+k.val, by omega⟩ = ⟨c+k.val,by omega⟩ := by
    apply Fin.ext
    simp [shuffle,show ¬ c+2+k.val < c by omega,show ¬ c+2+k.val < c+2 by omega]
    omega
  rw [hsh]
  simp [querySlots,active,earlyReserve,show c+k.val < a by omega]

def rectSlots (hce : c+e=a) (j : Fin m) : Fin (c+(2+e)) ↪ Spot (Fin (a+m+a)) :=
  ⟨active hce j, active_injective _ _⟩

theorem view_reserveShift (hce : c+e=a) (j : Fin m) (x : Duplex (Fin (a+m+a)) R) :
    view (rectSlots hce j) (reserveShift hce x) = view (querySlots a j) x ∘ shuffle hce := by
  funext i
  exact (hear_moveSlots hce x (active hce j i)).trans (congrArg (hear x) (switch_active hce j i))


private theorem switch_query (hce : c+e=a) (j : Fin m) (k : Fin (a+2)) :
    switchSpot hce (querySlots a j k) = active hce j ((shuffle hce).symm k) := by
  have h := switch_active hce j ((shuffle hce).symm k)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, switch_involutive hce]

/-- Conjugate an arbitrary rectangle-active update by the actual reserve exchange.
The original query receives the conjugated transformation, and all remaining
coordinates, including occupied late spares, are restored. -/
theorem conjugate_reserveShift (hce : c+e=a) (j : Fin m)
    (F : (Fin (c+(2+e)) → R) → Fin (c+(2+e)) → R) (x : Duplex (Fin (a+m+a)) R) :
    reserveShift hce (update (rectSlots hce j) F (reserveShift hce x)) =
      update (querySlots a j) (fun z => F (z ∘ shuffle hce) ∘ (shuffle hce).symm) x := by
  apply eq_update
  · intro k
    change hear (moveSlots hce _) _ = _
    rw [hear_moveSlots,switch_query]
    change hear (update (rectSlots hce j) F _) (rectSlots hce j _) = _
    rw [update_selected,view_reserveShift]
    rfl
  · intro u hu
    change hear (moveSlots hce _) u = _
    rw [hear_moveSlots]
    have hn : ∀ i, switchSpot hce u ≠ rectSlots hce j i := by
      intro i hi
      have hi' := congrArg (switchSpot hce) hi
      exact hu (shuffle hce i) (((switch_involutive hce u).symm.trans hi').trans (switch_active hce j i))
    rw [update_outside _ _ _ _ hn]
    change hear (moveSlots hce x) _ = _
    rw [hear_moveSlots,switch_involutive hce]

/-- All early reserve fields, independent of which main pair is queried. -/
def earlySlots (a m : ℕ) : Fin a ↪ Spot (Fin (a+m+a)) where
  toFun i := (false,⟨i.val,by omega⟩)
  inj' _ _ h := Fin.ext (congrArg (fun s => s.2.val) h)

@[simp] theorem querySlots_early (a : ℕ) (j : Fin m) (i : Fin a) :
    querySlots a j (Fin.castAdd 2 i) = earlySlots a m i := by
  exact active_complement (c:=a) (e:=0) (Nat.add_zero a) j i

/-- Apply the reserve basis change to the first block of the original query vector. -/
def reserveBlock (P : (Fin a → R) → Fin a → R) (z : Fin (a+2) → R) : Fin (a+2) → R :=
  Fin.append (P (z ∘ Fin.castAdd 2)) (z ∘ Fin.natAdd a)

/-- The field vector after preparation, expressed in physical `C, H, N, E`
order. The dimensions `a` and `c+e` can be propositionally equal. -/
theorem reserveBlock_shuffle (hce : c+e=a)
    (P : (Fin a → R) → Fin a → R) (z : Fin (a+2) → R) :
    reserveBlock P z ∘ shuffle hce =
      Fin.append (fun i => P (z ∘ Fin.castAdd 2) (Fin.cast hce (Fin.castAdd e i)))
        (Fin.append (z ∘ Fin.natAdd a)
          (fun k => P (z ∘ Fin.castAdd 2) (Fin.cast hce (Fin.natAdd c k)))) := by
  funext i
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun j => ?_) (fun k => ?_)) i
  · simp [reserveBlock,shuffle_first]
  · simp [reserveBlock,shuffle_middle]
  · simp [reserveBlock,shuffle_last]

theorem update_reserveBlock (P : (Fin a → R) → Fin a → R) (j : Fin m)
    (x : Duplex (Fin (a+m+a)) R) :
    update (earlySlots a m) P x = update (querySlots a j) (reserveBlock P) x := by
  apply eq_update
  · refine Fin.addCases (fun i => ?_) (fun k => ?_)
    · rw [querySlots_early, update_selected]
      simp only [reserveBlock, Fin.append_left]
      congr 2
      funext l
      exact congrArg (hear x) (querySlots_early a j l).symm
    · have hn : ∀ i, querySlots a j (Fin.natAdd a k) ≠ earlySlots a m i := by
        intro i heq
        rw [← querySlots_early a j i] at heq
        have h := congrArg Fin.val ((querySlots a j).injective heq)
        simp only [Fin.val_natAdd, Fin.val_castAdd] at h
        omega
      rw [update_outside _ _ _ _ hn]
      simp [reserveBlock, view]
  · intro u hu
    apply update_outside
    intro i
    exact (querySlots_early a j i) ▸ hu (Fin.castAdd 2 i)

/-- The full diagram at arbitrary occupied addresses. The first two operations
prepare the endpoint once. Only `F` changes with the query while inside the
rectangle layout; `C` sends that layout to the same common address for all
endpoints. -/
theorem physical_diagram (hce : c+e=a) (j : Fin m)
    (P : (Fin a → R) → Fin a → R) (F : (Fin (c+(2+e)) → R) → Fin (c+(2+e)) → R)
    (C : (Fin (c+(2+e)) → R) → Fin (a+2) → R) (S : (Fin (a+2) → R) → Fin (a+2) → R)
    (h : ∀ z, C (F (reserveBlock P z ∘ shuffle hce)) = S z) (x : Duplex (Fin (a+m+a)) R) :
    reserveShift hce
      (update (rectSlots hce j) (fun v => C v ∘ shuffle hce)
        (update (rectSlots hce j) F (reserveShift hce (update (earlySlots a m) P x)))) =
      update (querySlots a j) S x := by
  rw [update_comp,conjugate_reserveShift,update_reserveBlock P j,update_comp]
  congr 1
  funext z k
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun (h z) k

end InterchangeStageLift

end NearSquareRoot
end Computability
end OAI
