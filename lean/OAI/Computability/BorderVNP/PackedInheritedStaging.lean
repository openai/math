import OAI.Computability.BorderVNP.PackedInheritedState

/-! # Unique staging for an inherited interval layer

The old site can still have its own nondeterministic private choices. For each
such choice and each current physical input there is exactly one extension
to the added old incidence slots. Summing the actual sparse interpreter over
the larger bank therefore recovers its old table on the reconstructed words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open scoped Classical

/-- A complete site-local finite bank, extended by zero outside its allocated extent. -/
def bits {a b : ℕ} (work : Fin a → Bool) (input : Fin b → Bool) (k : ℕ) : Bool :=
  if h : k < a+b then Fin.append work input ⟨k,h⟩ else false

private theorem bits_left {a b : ℕ} (work : Fin a → Bool) (input : Fin b → Bool) (i : Fin a) :
    bits work input i.val = work i := by
  rw [bits,dite_eq_left (i.isLt.trans_le (Nat.le_add_right _ _))]
  exact Fin.append_left work input i

private theorem bits_right {a b : ℕ} (work : Fin a → Bool) (input : Fin b → Bool) (i : Fin b) :
    bits work input (a+i.val) = input i := by
  rw [bits,dite_eq_left (Nat.add_lt_add_left i.isLt a)]
  exact Fin.append_right work input i

/-- Evidence that the static interval list copies precisely the named old input from
the new incidence array. Many lanes can share one compressed record. -/
structure Covers (old next : ℕ) (cuts : List Slice) (read : Fin old → Fin next) : Prop where
  /-- Each clipped interval stays inside the old input. -/
  oldFit : ∀ p ∈ cuts, p.oldStart+p.width ≤ old
  /-- Each canonical source slice stays inside the new input. -/
  newFit : ∀ p ∈ cuts, p.newStart+p.width ≤ next
  /-- Every lane in the interval denotes the specified physical source. -/
  agrees : ∀ p (hp : p ∈ cuts) (i : Fin p.width),
    (read ⟨p.oldStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le (oldFit p hp)⟩).val = p.newStart+i.val
  /-- Every old lane occurs in at least one emitted row. -/
  covers : ∀ k : Fin old, ∃ p ∈ cuts, ∃ i : Fin p.width, p.oldStart+i.val = k.val

/-- The site's complete observable behavior depends only on its own finite bank.
This locality is preserved when more sparse layers are added. -/
def Site.Local (s : Site) : Prop :=
  ∀ (a b : ℕ → Bool), (∀ i < s.size, a i = b i) → s.observe a = s.observe b

private theorem tie_iff (s : Site) {n : ℕ} (p : Slice)
    (h₁ : p.oldStart+p.width ≤ s.incoming) (h₂ : p.newStart+p.width ≤ n)
    (g : Fin s.work → Bool) (old : Fin s.incoming → Bool) (new : Fin n → Bool) :
    (p.record s).Valid s.boxes (bits (Fin.append g old) new) ↔
      ∀ i : Fin p.width,
        old ⟨p.oldStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₁⟩ =
        new ⟨p.newStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₂⟩ := by
  have left (i : Fin p.width) :
      bits (Fin.append g old) new (s.work + (p.oldStart+i.val)) =
      old ⟨p.oldStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₁⟩ := by
    let j : Fin s.incoming := ⟨p.oldStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₁⟩
    exact (bits_left (Fin.append g old) new (j.natAdd s.work)).trans (Fin.append_right g old j)
  have right (i : Fin p.width) :
      bits (Fin.append g old) new (s.size + (p.newStart+i.val)) =
      new ⟨p.newStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₂⟩ :=
    bits_right (Fin.append g old) new ⟨p.newStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le h₂⟩
  constructor
  · intro h i
    have he := h 0 (by decide) i i.isLt
    simp only [Port.atBit,zero_mul,add_zero,mul_one,Nat.add_assoc] at he
    exact (left i).symm.trans (he.trans (right i))
  · intro h copy hcopy k hk
    let i : Fin p.width := ⟨k,hk⟩
    simpa only [Slice.record,Port.atBit,mul_zero,add_zero,mul_one,Nat.add_assoc] using
      (left i).trans ((h i).trans (right i).symm)

/-- The genuine interval checks uniquely determine all added staging bits. -/
theorem ties_iff (s : Site) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read)
    (g : Fin s.work → Bool) (old : Fin s.incoming → Bool) (new : Fin n → Bool) :
    (∀ p ∈ cuts, (p.record s).Valid s.boxes (bits (Fin.append g old) new)) ↔ old = new ∘ read := by
  constructor
  · intro h
    funext k
    obtain ⟨p,hp,i,hk⟩ := cover.covers k
    have ht := (tie_iff s p (cover.oldFit p hp) (cover.newFit p hp) g old new).mp (h p hp) i
    let o : Fin s.incoming := ⟨p.oldStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le (cover.oldFit p hp)⟩
    have he : o = k := Fin.ext hk
    have hn : read o = ⟨p.newStart+i.val,(Nat.add_lt_add_left i.isLt _).trans_le (cover.newFit p hp)⟩ := Fin.ext (cover.agrees p hp i)
    exact (congrArg old he).symm.trans (ht.trans ((congrArg new hn).symm.trans (congrArg (new ∘ read) he)))
  · rintro rfl p hp
    apply (tie_iff s p (cover.oldFit p hp) (cover.newFit p hp) g _ new).mpr
    intro i
    exact congrArg new (Fin.ext (cover.agrees p hp i))

/-- A correctly staged site has exactly the old observation, while any incorrect
extension is rejected by the actual interval records. -/
theorem observe_layer (s : Site) (locality : s.Local) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read) (g : Fin s.work → Bool) (old : Fin s.incoming → Bool)
    (new : Fin n → Bool) :
    (s.retain n cuts).observe (bits (Fin.append g old) new) =
      if old = new ∘ read then s.observe (bits g old) else none := by
  rw [s.observe_retain]
  have he := ties_iff s cuts read cover g old new
  by_cases h : old = new ∘ read
  · rw [ite_eq_left (he.mpr h),ite_eq_left h]
    apply locality
    intro i hi
    change i < s.work + s.incoming at hi
    rw [bits_left (Fin.append g old) new ⟨i,hi⟩,bits,dite_eq_left hi]
  · simp only [ite_eq_right (fun y => h (he.mp y)),ite_eq_right h]

/-- The older checks, observations, and new incidence equalities all remain local to the enlarged bank. -/
theorem Site.local_retain (s : Site) (loc : s.Local) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read) : (s.retain n cuts).Local := by
  intro a b h
  have old := loc a b (fun i hi => h i (hi.trans_le (Nat.le_add_right _ _)))
  have agrees (p : Slice) (hp : p ∈ cuts) : (p.record s).Valid s.boxes a ↔ (p.record s).Valid s.boxes b := by
    change (∀ c < 1, ∀ k < p.width, a _ = a _) ↔ (∀ c < 1, ∀ k < p.width, b _ = b _)
    apply forall_congr'; intro c
    apply imp_congr_right; intro _
    apply forall_congr'; intro k
    apply imp_congr_right; intro hk
    have h₁ := (Nat.add_lt_add_left hk p.oldStart).trans_le (cover.oldFit p hp)
    have h₂ := (Nat.add_lt_add_left hk p.newStart).trans_le (cover.newFit p hp)
    simp only [Port.atBit,mul_zero,add_zero,mul_one,Nat.add_assoc]
    rw [h _ ((Nat.add_lt_add_left h₁ s.work).trans_le (Nat.le_add_right s.size n)),h _ (Nat.add_lt_add_left h₂ s.size)]
  simp only [Site.observe_retain,old]
  congr 1
  exact propext (forall_congr' fun p => forall_congr' fun hp => agrees p hp)

/-- Local table read after summing its own private choices. Signed and tagged values
can interpret the same successful observation sequence. -/
noncomputable def Site.value {R : Type*} [AddCommMonoid R] (s : Site) (weight : List (Bool × Option ℕ) → R)
    (input : Fin s.incoming → Bool) : R :=
  ∑ work : Fin s.work → Bool, (s.observe (bits work input)).elim 0 weight

/-- The physical value of a retained sparse site is exactly its former table on the
reconstructed old wires. The equality holds for all exterior assignments and arbitrary
commutative additive target values. -/
theorem value_retain {R : Type*} [AddCommMonoid R] (s : Site) (loc : s.Local) {n : ℕ}
    (cuts : List Slice) (read : Fin s.incoming → Fin n) (cover : Covers s.incoming n cuts read)
    (weight : List (Bool × Option ℕ) → R) (new : Fin n → Bool) :
    (s.retain n cuts).value weight new = s.value weight (new ∘ read) := by
  classical
  let term (work : Fin (s.work+s.incoming) → Bool) := ((s.retain n cuts).observe (bits work new)).elim 0 weight
  change (∑ work, term work) = _
  rw [← (Fin.appendEquiv (α := Bool) s.work s.incoming).sum_comp term,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  change (∑ old, ((s.retain n cuts).observe (bits (Fin.append g old) new)).elim 0 weight) = _
  simp_rw [observe_layer s loc cuts read cover]
  rw [Finset.sum_eq_single (new ∘ read)]
  · simp
  · intro old _ h; simp [h]
  · simp

end Packing.Inherited

end BorderVNP
end Computability
end OAI
