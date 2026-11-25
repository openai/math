import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import Mathlib.Data.List.OfFn

section
/-!
# Matching uniquely addressed messages

The active and direction bits precede the payload and identifier.
Only the two flags and the identifier are sent through the ordinary
sorting network. Reversing active directions must permute the full
records, so both ends carry identical data.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Messages

abbrev row (H w : ℕ) := word (H + w + 2)

def identifier (H : ℕ) : (w : ℕ) → Val (word (H + w)) → Val (word H)
  | 0, x => x
  | w + 1, x => identifier H w x.2

def header (H w : ℕ) (x : Val (row H w)) : Val (word (H + 2)) :=
  (x.1, x.2.1, identifier H w x.2.2)

def reverse (H w : ℕ) (x : Val (row H w)) : Val (row H w) :=
  (x.1, if x.1 then !x.2.1 else x.2.1, x.2.2)

def valid (j H w : ℕ) (x : Val (tree j (row H w))) : Prop :=
  ((flatten j x).map (header H w)).Nodup ∧ ((flatten j x).map (reverse H w)).Perm (flatten j x)

theorem reverse_involutive (H w : ℕ) : Function.Involutive (reverse H w) := by
  rintro ⟨_ | _, b, y⟩ <;> simp [reverse]

theorem valid_iff (j H w : ℕ) (x : Val (tree j (row H w))) :
    valid j H w x ↔ ((flatten j x).map (header H w)).Nodup ∧
      ∀ r ∈ flatten j x, r.1 = true → reverse H w r ∈ flatten j x := by
  constructor
  · exact fun h => ⟨h.1, fun _ hr _ => h.2.subset (List.mem_map_of_mem hr)⟩
  · rintro ⟨hn, hm⟩
    refine ⟨hn, ?_⟩
    have hd := (hn.of_map (header H w)).map (reverse_involutive H w).injective
    apply (hd.subperm ?_).perm_of_length_le (by simp)
    rintro _ h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    cases ha : r.1
    · have he : reverse H w r = r := by
        unfold reverse
        rw [ite_eq_right (by simp [ha])]
      rw [he]
      exact hr
    · exact hm r hr ha

variable (F : Type) [Field F]

private theorem id_net (H w : ℕ) :
    DNet F (word (H + w)) (word H) (identifier H w) (H + w) := by
  induction w with
  | zero => exact (DNet.id F (word H)).mono (by simp)
  | succ w ih =>
    have t := ((DNet.discard F .bit).par ih).post ((Rewire.swap _ _).comp (.unit _))
    exact t.mono (by simp [wd]; omega)

private theorem header_net (H w : ℕ) :
    DNet F (row H w) (word (H + 2)) (header H w) (H + w + 2) := by
  have bit := DNet.id F .bit
  exact (bit.par (bit.par (id_net F H w))).mono (by simp [wd]; omega)

theorem reverse_net (H w : ℕ) : DNet F (row H w) (row H w) (reverse H w) (H + w + 6) := by
  have gate := DNet.table F (.pair .bit .bit) .bit
    (fun x => if x.1 then !x.2 else x.2) (by decide)
  have t := ((DNet.fst F .bit .bit).pair gate).par (DNet.id F (word (H + w)))
  exact ((t.pre (.assoc' _ _ _)).post (.assoc _ _ _)).mono (by simp [wd]; omega)

open Classical in
theorem net {F : Type} [Field F] {j H w m : ℕ} (ht : Radix.Tag F j (H + w + 2) m) :
    ∃ v ≤ m + 10000 * 2 ^ j * (w + (1 + H) * (j + 1) ^ 2),
      Net F (tree j (word (H + w + 2))) .unit (fun x _ => if valid j H w x then 1 else 0) v := by
  let t := tree j (row H w)
  have heads := (Tagged.mapRows_net (header_net F H w) j).comp (nodup_net F j (H + 2))
  have pair := (DNet.id F t).pair (Tagged.mapRows_net (reverse_net F H w) j)
  obtain ⟨r, hr, prep⟩ := pair.pair heads
  obtain ⟨k, v, hk, hv, hcheck⟩ := Install.blind ht
  have pin := Net.table (F := F) .bit .unit (fun b _ => if b then 1 else 0) (by decide)
  have h := prep.comp (((Install.uncurry hk).par pin).post (.unit' _))
  refine ⟨r + (v + wd t + 1), ?_, ?_⟩
  · have := Nat.two_pow_pos j
    simp only [t, row, wd_tree] at hr ⊢
    rw [wd_word] at hr ⊢
    ring_nf at hr hv ⊢
    omega
  · convert h using 1
    funext x _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      decide_eq_true_eq, Tagged.flatten_mapRows]
    by_cases hn : ((flatten j x).map (header H w)).Nodup
    · rw [hcheck _ _ (hn.of_map _)]
      simp [valid, Tagged.permuted, Tagged.flatten_mapRows, hn]
    · simp [valid, hn]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Messages
end

section
/-!
# Equality links implemented by packets

Select the headers and their pairing before reading payloads. Once
those headers are checked, the global permutation test imposes exactly
the indicated bit equalities between opposite ends of each active key.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Messages

def appendWord (H : ℕ) : (w : ℕ) → Val (word w) → Val (word H) → Val (word (H + w))
  | 0, _, a => a
  | w + 1, x, a => (x.1, appendWord H w x.2 a)

def assemble {H w : ℕ} (a : Val (word (H + 2))) (v : Val (word w)) : Val (row H w) :=
  (a.1, a.2.1, appendWord H w v a.2.2)

def opposite {H : ℕ} (a : Val (word (H + 2))) : Val (word (H + 2)) :=
  (a.1, if a.1 then !a.2.1 else a.2.1, a.2.2)

theorem header_assemble {H w : ℕ} (a : Val (word (H + 2))) (v : Val (word w)) :
    header H w (assemble a v) = a := by
  suffices identifier H w (appendWord H w v a.2.2) = a.2.2 by
    exact Prod.ext rfl (Prod.ext rfl this)
  induction w with
  | zero => rfl
  | succ w ih => exact ih v.2

theorem reverse_assemble {H w : ℕ} (a : Val (word (H + 2))) (v : Val (word w)) :
    reverse H w (assemble a v) = assemble (opposite a) v := rfl

theorem assemble_injective {H w : ℕ} (a : Val (word (H + 2))) :
    Function.Injective (assemble (w := w) a) := by
  suffices Function.Injective (fun x => appendWord H w x a.2.2) from
    fun _ _ h => this (congrArg (fun k => k.2.2) h)
  induction w with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ w ih =>
    intro x y h
    change (x.1, appendWord H w x.2 a.2.2) = (y.1, appendWord H w y.2 a.2.2) at h
    exact Prod.ext (Prod.mk.inj h).1 (ih (Prod.mk.inj h).2)

structure Delivery (j H : ℕ) where
  head : Fin (2 ^ j) → Val (word (H + 2))
  unique : Function.Injective head
  peer : Fin (2 ^ j) → Fin (2 ^ j)
  pairs : ∀ i, (head i).1 = true → head (peer i) = opposite (head i)

namespace Delivery
variable {j H w : ℕ} (p : Delivery j H)

theorem valid_iff {m : Val (tree j (row H w))} (v : Fin (2 ^ j) → Val (word w))
    (hm : flatten j m = List.ofFn (fun i => assemble (p.head i) (v i))) :
    valid j H w m ↔ ∀ i, (p.head i).1 = true → v (p.peer i) = v i := by
  rw [Messages.valid_iff, hm, List.map_ofFn]
  have hu : (List.ofFn (header H w ∘ fun i => assemble (p.head i) (v i))).Nodup := by
    rw [show (header H w ∘ fun i => assemble (p.head i) (v i)) = p.head from
      funext fun i => header_assemble _ _]
    exact List.nodup_ofFn.mpr p.unique
  refine ⟨?_, fun h => ⟨hu, ?_⟩⟩
  · intro h i hi
    have he := h.2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩) hi
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
    rw [reverse_assemble, ← p.pairs _ hi] at hk
    have h' := congrArg (header H w) hk
    simp only [header_assemble] at h'
    have := p.unique h'
    subst k
    exact assemble_injective _ hk
  · intro r hr hi
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact List.mem_ofFn.mpr ⟨p.peer i, by rw [p.pairs i hi, h i hi, reverse_assemble]⟩

variable {A : Type} (tap : Fin (2 ^ j) → slots (word w) → A)

def link (a b : A) : Prop :=
  ∃ i k, (p.head i).1 = true ∧ tap (p.peer i) k = a ∧ tap i k = b

theorem checks {m : Val (tree j (row H w))} (z : A → Bool)
    (hm : flatten j m = List.ofFn (fun i =>
      assemble (p.head i) ((bits (word w)).symm (z ∘ tap i)))) :
    valid j H w m ↔ ∀ a b, p.link tap a b → z a = z b := by
  rw [p.valid_iff _ hm]
  constructor
  · rintro h _ _ ⟨i, k, hi, rfl, rfl⟩
    exact congrFun ((bits (word w)).symm.injective (h i hi)) k
  · intro h i hi
    exact congrArg (bits (word w)).symm (funext fun k => h _ _ ⟨i, k, hi, rfl, rfl⟩)

end Delivery
end OAI.LinearAlgebra.MatrixExponent.Transcript.Messages
end
