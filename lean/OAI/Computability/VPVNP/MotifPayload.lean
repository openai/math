import OAI.Computability.VPVNP.MotifLocalSelectors
import Mathlib.Algebra.BigOperators.Fin

/-!
# Grouping repeated motif maps by the total edge payload

Theorem 6.1 uses one outer term for each total supply-width vector. The
wire on an edge contains a selector list and the concatenated fields for
the selected base maps. The coordinate arithmetic below is mixed-radix
binary concatenation in the order of the copies.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector

open WireTensor

variable {J E S C₀ : Type*} {C : J → Type*}

/-- A width-`b` wire coordinate, numbered by its binary word. -/
abbrev Word (b : ℕ) := Fin (2 ^ b)

/-- Mixed-radix decomposition into the fields for consecutive copies. -/
def unpackFields {u : ℕ} (w : Fin u → ℕ) : Word (∑ i, w i) ≃ ∀ i, Word (w i) :=
  (finCongr (Finset.prod_pow_eq_pow_sum Finset.univ w 2).symm).trans finPiFinEquiv.symm

/-- The payload occupies the low bits, with the list of selectors above it. -/
def wireFields (u bits v : ℕ) : Word (v + u * bits) ≃ (Fin u → Word bits) × Word v :=
  (((finFunctionFinEquiv.prodCongr (Equiv.refl (Word v))).trans finProdFinEquiv).trans
    (finCongr (show (2 ^ bits) ^ u * 2 ^ v = 2 ^ (v + u * bits) by
      rw [pow_add, Nat.mul_comm u bits, pow_mul, Nat.mul_comm]))).symm

/-- Each edge's accumulated payload width. -/
def totalWidth (w : S → E → ℕ) {u : ℕ} (θ : Fin u → S) (e : E) : ℕ := ∑ i, w (θ i) e

/-- The complete list of table lookups for a single party. Each copy selects
one base map and supplies its output and input coordinates. -/
abbrev EntryIndices (G : Supply J E) (C : J → Type*) (w : S → E → ℕ) (u : ℕ) (j : J) :=
  (i : Fin u) → Σ s : S, C j × Half G (fun e => Word (w s e)) j

/-- Split the payload only if its total width agrees on every supply edge. -/
noncomputable def payloadIndices (G : Supply J E) (w : S → E → ℕ) {u : ℕ} (v : E → ℕ)
    (θ : Fin u → S) (j : J) (c : Fin u → C j) (x : Half G (fun e => Word (v e)) j) :
    Option (EntryIndices G C w u j) := by
  classical
  exact if hv : v = totalWidth w θ then some (fun i =>
    ⟨θ i, c i, mapHalf G (fun e y =>
      unpackFields (fun l => w (θ l) e) (Fin.cast (congrArg (2 ^ ·) (congrFun hv e)) y) i) x⟩)
  else none

/-- Encode the selectors for all copies using the same fixed code table. -/
def sequenceCode {T : Type*} (code : S ↪ T) (u : ℕ) : (Fin u → S) ↪ (Fin u → T) where
  toFun θ := fun i => code (θ i)
  inj' _ _ h := funext fun i => code.injective (congrFun h i)

/-- Invalid tags reject the entry. Membership in the image can be checked
copy by copy against the fixed finite table. -/
noncomputable def tagIndices (G : Supply J E) (w : S → E → ℕ) {u bits : ℕ}
    (code : S ↪ Word bits) (v : E → ℕ) (tags : Fin u → Word bits) (j : J)
    (c : Fin u → C j) (x : Half G (fun e => Word (v e)) j) :
    Option (EntryIndices G C w u j) := by
  classical
  exact if ht : tags ∈ Set.range (sequenceCode code u) then
    payloadIndices G w v ht.choose j c x else none

/-- The scalar-independent evaluator description at a party, including all
checks on the selector copies, their validity and the supplied widths. -/
noncomputable def groupedIndices (G : Supply J E) (w : S → E → ℕ) {u bits : ℕ}
    (code : S ↪ Word bits) (v : E → ℕ) (j : J) (c : Fin u → C j)
    (x : Half G (fun e => Word (v e + u * bits)) j) : Option (EntryIndices G C w u j) := by
  classical
  let fields := mapHalf G (fun e => wireFields u bits (v e)) x
  exact if HalfAgrees G j fields then
    tagIndices G w code v (readAnchor G j fields).1 j c (mapHalf G (fun _ => Prod.snd) fields)
  else none

/-- Evaluate a successful list of base entries multiplicatively. Failed checks
produce the zero scalar in any commutative semiring. -/
def evalIndices {R : Type*} [CommMonoidWithZero R] {G : Supply J E} {w : S → E → ℕ}
    (L : ∀ s j, C j → Half G (fun e => Word (w s e)) j → R) (j : J) {u : ℕ}
    (x : Option (EntryIndices G C w u j)) : R :=
  x.elim 0 fun t => ∏ i, L (t i).1 j (t i).2.1 (t i).2.2

/-- The map in one term of the grouped motif identity. -/
noncomputable def groupedMap {R : Type*} [CommMonoidWithZero R] (G : Supply J E)
    (w : S → E → ℕ) (L : ∀ s j, C j → Half G (fun e => Word (w s e)) j → R)
    {u bits : ℕ} (code : S ↪ Word bits) (v : E → ℕ) (j : J) (c : Fin u → C j)
    (x : Half G (fun e => Word (v e + u * bits)) j) : R :=
  evalIndices L j (groupedIndices G w code v j c x)

/-- The common code-table membership test is equivalent to testing each
selector separately. Decoding requires no search over selector sequences. -/
theorem mem_sequenceCode_range {T : Type*} {u : ℕ} (code : S ↪ T) (t : Fin u → T) :
    t ∈ Set.range (sequenceCode code u) ↔ ∀ i, t i ∈ Set.range code := by
  constructor
  · rintro ⟨θ, rfl⟩ i
    exact ⟨θ i, rfl⟩
  · intro h
    exact ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec⟩

end MotifSelector

end VPVNP
end Computability
end OAI
