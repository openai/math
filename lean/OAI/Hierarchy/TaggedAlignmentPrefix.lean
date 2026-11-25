import OAI.Hierarchy.TaggedAlignmentContract

namespace OAI
/-! # Local row rules determine the permutation of a whole padded block -/

namespace Hierarchy.Tagged.Align
open scoped Classical
noncomputable section

/-- The real sources occupy a prefix; the remaining sources are dummies. -/
def split {r m : ℕ} (room : r ≤ m) : Input r m ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le room))

@[simp] theorem split_real_val {r m : ℕ} (room : r ≤ m) (i : Fin r) :
    (split room (.inl i)).val = i.val := rfl
@[simp] theorem split_dummy_val {r m : ℕ} (room : r ≤ m) (i : Fin (m-r)) :
    (split room (.inr i)).val = r+i.val := rfl

def realAddress {d : ℕ} (p : ℕ) : {r : ℕ} → (Fin r → Fin d) → Fin r → ℕ
  | 0, _, i => Fin.elim0 i
  | _+1, k, i => dest p k i

def embed {r m d p : ℕ} (hp : 0 < p) (key : Fin r → Fin d) (ascending : Monotone key)
    (space : r + d*p ≤ m) : Fin r ↪ Fin m := by
  cases r with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  | succ n => exact ⟨fun i => ⟨dest p key i,(dest_lt_slots hp key ascending i).trans_le space⟩,
      fun i j e => (dest_strict hp key).injective (congrArg Fin.val e)⟩

@[simp] theorem embed_val {r m d p : ℕ} (hp : 0 < p) (key : Fin r → Fin d) (ascending : Monotone key)
    (space : r+d*p ≤ m) (i : Fin r) : (embed hp key ascending space i).val = realAddress p key i := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => rfl

/-- A predicate on neighbors in the physical source array, including the
first real address and increasing residual source destinations. -/
def LocalTags {m d : ℕ} (r p : ℕ) (key : Fin m → Fin d) (g : Fin m → Fin m) : Prop :=
  (∀ i, i.val=0 → i.val<r → (g i).val=0) ∧ ∀ i j : Fin m, i.val+1=j.val →
    (j.val<r → (g j).val = advance p (g i).val (decide (key i ≠ key j))) ∧
    (r ≤ i.val → g i < g j)

private theorem all_adjacent {s : ℕ} {β : Type*} [Preorder β] (f : Fin s → β)
    (h : ∀ i j, i.val+1 = j.val → f i < f j) : StrictMono f := by
  cases s with
  | zero => exact fun i => Fin.elim0 i
  | succ n => exact Fin.strictMono_iff_lt_succ.mpr (fun i => h _ _ rfl)

theorem local_iff {r m d p : ℕ} (room : r ≤ m) (key : Fin m → Fin d) (g : Fin m → Fin m)
    (e : Fin r ↪ Fin m) (place : ∀ i, (e i).val = realAddress p (fun j => key (split room (.inl j))) i) :
    LocalTags r p key g ↔ Fits e (g ∘ split room) := by
  constructor
  · rintro ⟨first, checks⟩
    constructor
    · cases r with
      | zero => exact fun i => Fin.elim0 i
      | succ n =>
        apply (adjacent_real_iff (fun j => key (split room (.inl j))) e place (fun j => g (split room (.inl j)))).mpr
        exact ⟨first _ rfl (Nat.zero_lt_succ n),fun i =>
          (checks (split room (.inl i.castSucc)) (split room (.inl i.succ)) rfl).1 i.succ.isLt⟩
    · apply all_adjacent
      intro i j next
      apply (checks (split room (.inr i)) (split room (.inr j)) (by simp; omega)).2
      simp
  · rintro ⟨real, dummy⟩
    constructor
    · intro i zero lt
      cases r with
      | zero => omega
      | succ n =>
        have ie : i = split room (.inl (0 : Fin (n+1))) := Fin.ext (by simpa using zero)
        rw [ie]
        have a := congrArg Fin.val (real (0 : Fin (n+1)))
        simpa [Function.comp_apply,place,realAddress,dest_zero] using a
    · intro i j succ
      constructor
      · intro jr
        cases r with
        | zero => omega
        | succ n =>
          let k : Fin n := ⟨i.val,by omega⟩
          have ix : i = split room (.inl k.castSucc) := Fin.ext rfl
          have jx : j = split room (.inl k.succ) := Fin.ext succ.symm
          rw [ix,jx]
          have steps := (adjacent_real_iff (fun u => key (split room (.inl u))) e place
            (fun u => g (split room (.inl u)))).mp real
          exact steps.2 k
      · intro ir
        let u : Fin (m-r) := ⟨i.val-r, by have := i.isLt; omega⟩
        let v : Fin (m-r) := ⟨j.val-r, by have := j.isLt; omega⟩
        have ix : i = split room (.inr u) := Fin.ext (by simp [u]; omega)
        have jx : j = split room (.inr v) := Fin.ext (by simp [v]; omega)
        rw [ix,jx]
        exact dummy (show u < v from by change i.val-r < j.val-r; omega)

theorem canonical_tags {r m d p : ℕ} (room : r ≤ m) (key : Fin m → Fin d) (g : Fin m → Fin m)
    (e : Fin r ↪ Fin m) (place : ∀ i, (e i).val = realAddress p (fun j => key (split room (.inl j))) i) :
    Function.Bijective g ∧ LocalTags r p key g ↔ g = (split room).symm.trans (complete e) := by
  rw [local_iff room key g e place, ← (split room).bijective_comp g, bijective_fits_iff]
  constructor
  · intro eq
    funext i
    simpa using congrFun eq ((split room).symm i)
  · rintro rfl
    funext i
    simp

end
end Hierarchy.Tagged.Align

end OAI
