import OAI.Computability.NearSquareRoot.KernelScaleBank

/-! # Natural ordinal layout of a physical scale bank

Every row extends its active address by independent prefix and suffix
spectators. Its natural ordinal numbers the entire flat array, while the
bits of the active ordinal supply the paired columns of the transform.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleLayout

open IntegerMultiplication KernelScaleStream
open KernelSelectorAlign (Column decode decode_length flatBits_decode)
open KernelScaleSpectator (expand)

/-- Recover the paired kernel columns in their physical high-to-low order. -/
def joinColumns {a : ℕ} : (h : ℕ) → List (Column a) → KernelPass.Addr (a+1) h
  | 0, _ => Fin.elim0
  | n+1, u::v::xs => Fin.cons (paired u v) (joinColumns n xs)
  | _+1, _ => fun _ _ _ => 0

theorem singleColumns_join {a h : ℕ} (cs : List (Column a)) (hl : cs.length = 2*h) :
    singleColumns (List.ofFn (joinColumns h cs)) = cs := by
  induction h generalizing cs with
  | zero =>
    have e : cs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst cs
    simp [singleColumns]
  | succ h ih =>
    rcases cs with _ | ⟨u, s⟩
    · simp at hl
    rcases s with _ | ⟨v, xs⟩
    · simp at hl
      omega
    have len : xs.length = 2*h := by simp only [List.length_cons] at hl; omega
    rw [joinColumns, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, singleColumns, List.flatMap_cons, List.cons_append,
      List.nil_append, split_paired_left, split_paired_right]
    exact congrArg (fun s => u::v::s) (ih xs len)

@[simp] theorem joinColumns_single {a h : ℕ} (x : KernelPass.Addr (a+1) h) :
    joinColumns h (singleColumns (List.ofFn x)) = x := by
  induction h with
  | zero => funext i; exact Fin.elim0 i
  | succ h ih =>
    rw [List.ofFn_succ]
    change Fin.cons (n := h) (α := fun _ => KernelPass.Column (a+1)) (paired (split a (x 0) 0) (split a (x 0) 1))
      (joinColumns h (singleColumns (List.ofFn (Fin.tail x)))) = _
    rw [paired_split, ih, Fin.cons_self_tail]

private theorem single_length {a h : ℕ} (x : KernelPass.Addr (a+1) h) :
    (singleColumns (List.ofFn x)).length = 2*h := by
  simp [singleColumns, List.length_flatMap, Function.comp_def, Nat.mul_comm]

/-- Decode the fixed-width MSF binary number of the active address. -/
def address (a h n : ℕ) : KernelPass.Addr (a+1) h :=
  joinColumns h (decode a (2*h) (Bits.phrase ((a+1)*(2*h)) n).reverse)

/-- The table position of every active ordinal has its physically decoded columns. -/
theorem address_get (a h n : ℕ) (hn : n < 2^((a+1)*(2*h))) :
    (KernelSelector.addressColumns a (2*h))[n]? =
      some (singleColumns (List.ofFn (address a h n))) := by
  let bits := (Bits.phrase ((a+1)*(2*h)) n).reverse
  have len : bits.length = (a+1)*(2*h) := by simp [bits, Bits.phrase_length]
  have cslen := decode_length a (2*h) bits len
  have e := addressColumns_get a (decode a (2*h) bits)
  rw [cslen, flatBits_decode _ _ _ len, endianness, List.reverse_reverse, Bits.value_phrase hn] at e
  change _ = some (singleColumns (List.ofFn (joinColumns h (decode a (2*h) bits))))
  rw [singleColumns_join _ cslen]
  exact e

/-- The inverse of active ordinal decoding, retaining the leading zeroes in each slot. -/
def rank {a h : ℕ} (x : KernelPass.Addr (a+1) h) : Fin (2^((a+1)*(2*h))) :=
  let bits := KernelSelectorAlign.flatBits a (singleColumns (List.ofFn x))
  ⟨bitValue bits, by
    rw [endianness]
    simpa [bits, single_length] using Bits.value_lt bits.reverse⟩

@[simp] theorem address_rank {a h : ℕ} (x : KernelPass.Addr (a+1) h) :
    address a h (rank x) = x := by
  have atRank := addressColumns_get a (singleColumns (List.ofFn x))
  rw [single_length] at atRank
  have decoded := address_get a h (rank x) (rank x).isLt
  have eq := congrArg (joinColumns h) (Option.some.inj (decoded.symm.trans atRank))
  simpa only [joinColumns_single] using eq

@[simp] theorem rank_address {a h : ℕ} (n : Fin (2^((a+1)*(2*h)))) :
    rank (address a h n) = n := by
  let bits := (Bits.phrase ((a+1)*(2*h)) n.val).reverse
  have len : bits.length = (a+1)*(2*h) := by simp [bits, Bits.phrase_length]
  apply Fin.ext
  change bitValue (KernelSelectorAlign.flatBits a (singleColumns
    (List.ofFn (joinColumns h (decode a (2*h) bits))))) = n.val
  rw [singleColumns_join _ (decode_length _ _ _ len), flatBits_decode _ _ _ len,
    endianness, List.reverse_reverse, Bits.value_phrase n.isLt]

/-- The active ordinal order covers every mathematical address exactly once. -/
def addressEquiv (a h : ℕ) : Fin (2^((a+1)*(2*h))) ≃ KernelPass.Addr (a+1) h where
  toFun := fun n => address a h n
  invFun := rank
  left_inv := rank_address
  right_inv := address_rank

/-- Given the suffix size, extract the active part of a full array index. -/
def coord (a h b n : ℕ) : KernelPass.Addr (a+1) h :=
  address a h ((n / b) % 2^((a+1)*(2*h)))

private theorem index_decomposition (n b m : ℕ) :
    (n / b / m)*(m*b) + (n / b % m)*b + n%b = n := by
  calc
    _ = (m*(n / b / m)+n/b%m)*b+n%b := by ring
    _ = n := by rw [Nat.div_add_mod, Nat.mul_comm, Nat.div_add_mod]

/-- Mapping the natural array ordinals to paired columns produces exactly
the order emitted by the physical selector and both spectator replications. -/
theorem ordinal_order (a h p b : ℕ) (hb : 0 < b) :
    (List.range (p*(2^((a+1)*(2*h))*b))).map
      (fun n => singleColumns (List.ofFn (coord a h b n))) =
      expand p b (KernelSelector.addressColumns a (2*h)) := by
  let m := 2^((a+1)*(2*h))
  have hm : 0 < m := by dsimp [m]; positivity
  have size : (KernelSelector.addressColumns a (2*h)).length = m := by
    simp [KernelSelector.addressColumns, m]
  apply List.ext_getElem?
  intro n
  by_cases hn : n < p*(m*b)
  · rw [List.getElem?_map, List.getElem?_range hn, Option.map_some]
    have hp : n/b/m < p := (Nat.div_lt_iff_lt_mul hm).mpr <|
      (Nat.div_lt_iff_lt_mul hb).mpr (by rwa [Nat.mul_assoc])
    have he := KernelScaleSpectator.expand_get hp
      (address_get a h (n/b%m) (Nat.mod_lt _ hm)) (Nat.mod_lt n hb)
    rw [size, index_decomposition] at he
    exact he.symm
  · rw [List.getElem?_eq_none (by simpa [m] using Nat.le_of_not_gt hn),
      List.getElem?_eq_none (by simpa [size] using Nat.le_of_not_gt hn)]

/-- A canonical bank layout from the three shape parameters. The independent
records receive consecutive natural labels even when their active tags agree. -/
def ordinal (a : ℕ) {I : Type} (h p b : I → ℕ)
    (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i) : KernelScaleBank.Layout a I ℕ where
  h := h
  prefixCount := p
  suffixCount := b
  prefix_pos := hp
  suffix_pos := hb
  rows i := List.range (p i*(2^((a+1)*(2*h i))*b i))
  coord i := coord a (h i) (b i)
  address_order i := ordinal_order a (h i) (p i) (b i) (hb i)

end KernelScaleLayout

end NearSquareRoot
end Computability
end OAI
