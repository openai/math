import OAI.Computability.BorderVNP.CoverMotionNumerator

/-!
# Executable residue-table correction for a quaternion frame motion

The two cleared motion quaternions and the inverse low representatives form
fixed finite data. Given only the high-level modular address, the correction
uses a table lookup, three modular quaternion products, and exact division of
the four output coefficients. The table has no dependence on the high level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

/-- Canonical nonnegative residue of a signed fixed-table entry. -/
def storedInt (m : ℕ) (z : ℤ) : ℕ :=
  if z < 0 then (m - z.natAbs % m) % m else z.natAbs % m

private theorem storedInt_correct (m : ℕ) (hm : 0 < m) (z : ℤ) :
    storedInt m z = (z : ZMod m).val := by
  let : NeZero m := ⟨hm.ne'⟩
  cases z with
  | ofNat n =>
    simp [storedInt,ZMod.val_natCast]
  | negSucc n =>
    have hh := Nat.mod_lt (n+1) hm
    have hneg : (Int.negSucc n : ℤ) < 0 := by omega
    simp only [storedInt,hneg,↓reduceIte,Int.natAbs_negSucc,Int.cast_negSucc]
    rw [← ZMod.val_natCast,Nat.cast_sub hh.le,ZMod.natCast_self,zero_sub,ZMod.natCast_mod]

/-- Canonical binary encoding of a fixed signed quaternion at the modulus
specified by the running instance. -/
def storedCoords (m : ℕ) (z : Order) : BinaryCoords :=
  (storedInt m z.re, storedInt m z.imI, storedInt m z.imJ, storedInt m z.imK)

/-- Stored constants reduce to the genuine quaternion residue coordinates. -/
theorem storedCoords_correct (l : ℕ) (z : Order) :
    storedCoords (7^l) z = binaryCoords l (reduce l z) := by
  simp only [storedCoords,storedInt_correct _ (show 0 < 7^l by positivity),binaryCoords,reduce,
    RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]

/-- Restrict a four-residue address to a lower modulus. -/
def lowCoords (m : ℕ) (z : BinaryCoords) : BinaryCoords :=
  (z.1%m,z.2.1%m,z.2.2.1%m,z.2.2.2%m)

private theorem low_word {l k : ℕ} (hk : k ≤ l) (z : ℤ) :
    (z : ZMod (7^l)).val % 7^k = (z : ZMod (7^k)).val := by
  let f := ZMod.castHom (Nat.pow_dvd_pow 7 hk) (ZMod (7^k))
  rw [← ZMod.val_natCast]
  apply congrArg ZMod.val
  calc
    _ = f (((z : ZMod (7^l)).val : ℕ) : ZMod (7^l)) := (map_natCast f _).symm
    _ = _ := by rw [ZMod.natCast_zmod_val,map_intCast]

/-- Reducing the four modular coordinates recovers the coordinates at every shallower level. -/
theorem lowCoords_correct {k l : ℕ} (hk : k ≤ l) (x : Order) :
    lowCoords (7^k) (binaryCoords l (reduce l x)) = binaryCoords k (reduce k x) :=
  Prod.ext (low_word hk _) (Prod.ext (low_word hk _) (Prod.ext (low_word hk _) (low_word hk _)))

private def key (l : ℕ) (v : Deck l) : BinaryCoords := binaryCoords l (deckAddress l v).val

private theorem key_injective (l : ℕ) : Function.Injective (key l) := by
  intro x y h
  apply deckAddress_injective l
  apply Units.ext
  apply QuaternionAlgebra.ext
  · exact ZMod.val_injective _ (congrArg Prod.fst h)
  · exact ZMod.val_injective _ (congrArg (fun z => z.2.1) h)
  · exact ZMod.val_injective _ (congrArg (fun z => z.2.2.1) h)
  · exact ZMod.val_injective _ (congrArg (fun z => z.2.2.2) h)

/-- The complete fixed inverse-representative table for one denominator
exponent. Its keys are canonical four-coordinate low addresses. -/
noncomputable def inverseTable (a : ℕ) : List (BinaryCoords × Order) :=
  (Finset.univ : Finset (Deck (1+2*a))).toList.map
    (fun v => (key (1+2*a) v, inverseRepresentative a v))

/-- Scan the fixed table. The fallback makes the operation total on malformed
addresses as well as on the valid quaternion tiles. -/
def lookupInverse (k : BinaryCoords) : List (BinaryCoords × Order) → Order
  | [] => 1
  | (v,g) :: tail => if k = v then g else lookupInverse k tail

private theorem lookup_map {S : Type*} (idx : S → BinaryCoords) (hidx : Function.Injective idx)
    (value : S → Order) (xs : List S) {x : S} (hx : x ∈ xs) :
    lookupInverse (idx x) (xs.map fun s => (idx s,value s)) = value x := by
  induction xs with
  | nil => simp at hx
  | cons s xs ih =>
    simp only [List.map_cons,lookupInverse]
    by_cases h : x = s
    · simp [h]
    · have hn : idx x ≠ idx s := fun he => h (hidx he)
      simpa only [hn,↓reduceIte] using ih ((List.mem_cons.mp hx).resolve_left h)

/-- Every valid tile retrieves its assigned integral low representative. -/
theorem lookupInverse_correct (a : ℕ) (v : Deck (1+2*a)) :
    lookupInverse (key (1+2*a) v) (inverseTable a) = inverseRepresentative a v :=
  lookup_map _ (key_injective _) _ _ (by simp)

/-- The four-coordinate procedure. The table and the two signed quaternions
are fixed for each motion. The varying inputs are the modulus and address. -/
def tableCorrection (a : ℕ) (u v : Order) (table : List (BinaryCoords × Order))
    (m : {n : ℕ // 0 < n}) (x : BinaryCoords) : BinaryCoords :=
  let δ := lookupInverse (lowCoords (7^(1+2*a)) x) table
  let t := binaryProduct (m, storedCoords m.val u, x)
  let r := binaryProduct (m, t, storedCoords m.val δ)
  divideCoords (7^(2*a)) (binaryProduct (m, r, storedCoords m.val v))

/-- The table calculation agrees with the matrix action for every valid input
tile and every output level of positive depth. -/
theorem tableCorrection_exact {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d)
    (u v : Order) (hu : (7:ℝ)^a • (g:Mat) = split u)
    (hv : (7:ℝ)^a • ((g⁻¹:SL):Mat) = split v) (input : Deck (d+2*a)) :
    tableCorrection a u v (inverseTable a) ⟨7^(d+2*a), by positivity⟩
      (binaryCoords _ (deckAddress _ input).val) =
      binaryCoords d (deckAddress d (motionDeck hg hd input)).val := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective ((gamma (d+2*a)).subgroupOf (gamma 1)) input
  change _ = binaryCoords d (deckAddress d (motionDeck hg hd (x : Deck (d+2*a)))).val
  rw [correctedUnit_address hg hd x]
  change tableCorrection _ _ _ _ _ (binaryCoords _ (reduce _ x.val.val)) =
    binaryCoords d (coordinates d (correctedUnit hg x).val)
  unfold tableCorrection
  rw [lowCoords_correct (show 1+2*a ≤ d+2*a by omega) x.val.val]
  change divideCoords _ (binaryProduct (_, binaryProduct (_, binaryProduct
    (_, storedCoords _ u, binaryCoords _ (reduce _ x.val.val)),
    storedCoords _ (lookupInverse (key _ (x : Deck (1+2*a))) (inverseTable a))), storedCoords _ v)) = _
  rw [lookupInverse_correct,storedCoords_correct,storedCoords_correct,storedCoords_correct,
    binaryProduct_correct,binaryProduct_correct,binaryProduct_correct]
  exact divided_numerator hg d u v hu hv x

end Cover.Frame

end BorderVNP
end Computability
end OAI
