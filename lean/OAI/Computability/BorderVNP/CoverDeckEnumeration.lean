import OAI.Computability.BorderVNP.CoverDeckAddress
import OAI.Computability.BorderVNP.CoverDeckRouting

/-!
# Listing all tile addresses using congruence digits

Lemma 5.1 can be implemented without a visited-address dictionary. Each
first-layer tile has a fixed representative, and each subsequent digit is a
triple modulo seven. Repeated seventh powers of a fixed depth-two table give
all these digits. All multiplications in the listing algorithm take place
modulo the final level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- Raise to the seventh power once per congruence level. -/
def seventhIterate {M : Type*} [Monoid M] : ℕ → M → M
  | 0, x => x
  | n+1, x => (seventhIterate n x)^7

private theorem map_seventh {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (n : ℕ) (x : M) : f (seventhIterate n x) = seventhIterate n (f x) := by
  induction n <;> simp [seventhIterate, *]

/-- Enumerate the products of a first-layer table and `d` successive digit
tables. Each stage computes the digit powers once and shares them among all
prefixes. -/
def expandDigits {M : Type*} [Monoid M] (first digits : List M) : ℕ → List M
  | 0 => first
  | d+1 =>
    let layer := digits.map (seventhIterate d)
    (expandDigits first digits d).flatMap (fun x => layer.map (x * ·))

private theorem expand_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (a b : List M) (d : ℕ) :
    (expandDigits a b d).map f = expandDigits (a.map f) (b.map f) d := by
  induction d with
  | zero => rfl
  | succ d h =>
    simp only [expandDigits, List.map_flatMap, ← h, List.flatMap_map, List.map_map,
      Function.comp_def, map_mul, map_seventh]

/-- The length of the list is the initial count times the radix to the number
of digit levels. -/
theorem expand_length {M : Type*} [Monoid M] (a b : List M) (d : ℕ) :
    (expandDigits a b d).length = a.length * b.length^d := by
  induction d with
  | zero => simp [expandDigits]
  | succ d h =>
    simp only [expandDigits, List.length_flatMap, List.length_map]
    change (List.map (Function.const M b.length) (expandDigits a b d)).sum = _
    rw [List.map_const, List.sum_replicate, h, nsmul_eq_mul, Nat.cast_id, pow_succ, mul_assoc]

/-- The finite table of first-layer representatives, fixed for every instance. -/
noncomputable def firstTable : List Orderˣ := by
  classical
  exact Finset.univ.toList.map (fun r => (liftFirst r).val)

/-- The 343 fixed depth-two lifts used to form higher congruence digits. -/
noncomputable def digitTable : List Orderˣ := by
  classical
  exact Finset.univ.toList.map (fun r => (liftBase 0 r).val)

/-- The initial table has exactly one entry per first-layer tile. -/
theorem first_length : firstTable.length = tileCount 2 := by
  classical
  rw [tileCount,Subgroup.relIndex,← leading_kernel 0,Subgroup.index_ker,Nat.card_eq_fintype_card]
  simp [firstTable]

/-- The branching number of the enumerator is exactly seven cubed. -/
theorem digit_length : digitTable.length = 7^3 := by
  classical
  simp [digitTable,Layer]

private theorem lift_by_power (d : ℕ) (r : Layer) : ∃ x : gamma (d+2),
    x.val = seventhIterate d (liftBase 0 r).val ∧ (leading (d+1) x).toAdd = r := by
  induction d with
  | zero =>
    exact ⟨liftBase 0 r,rfl,congrArg Multiplicative.toAdd (leading_surj 0 (.ofAdd r)).choose_spec⟩
  | succ d ih =>
    obtain ⟨x,hx,hl⟩ := ih
    let a := coefficient (d+2) x
    have ha : x.val.val = atDepth (d+2) a := coefficient_spec _ x
    obtain ⟨b,hb,hr⟩ := depth_seventh (d+1) a
    let y : gamma (d+3) := ⟨x.val^7, by rw [Units.val_pow_eq_pow_val,norm_pow,x.2.1,one_pow],
      b,by rw [Units.val_pow_eq_pow_val,ha,hb]⟩
    have hc : coefficient (d+3) y = b := by
      apply atDepth_inj
      rw [← coefficient_spec]
      change (↑(x.val^7) : Order) = atDepth (d+3) b
      rw [Units.val_pow_eq_pow_val,ha,hb]
    refine ⟨y, by change x.val^7 = _; rw [hx]; rfl, ?_⟩
    change residues (coefficient (d+3) y) = r
    rw [hc,residues_congr hr]
    exact hl

private theorem integral_list_complete (d : ℕ) (g : gamma 1) :
    ∃ x ∈ expandDigits firstTable digitTable d, x⁻¹*g.val ∈ gamma (d+2) := by
  classical
  induction d with
  | zero =>
    let r := (leading 0).rangeRestrict g
    let s := liftFirst r
    have h : leading 0 s = leading 0 g :=
      congrArg Subtype.val ((leading 0).rangeRestrict_surjective r).choose_spec
    have hn := ((leading 0).eq_iff.mp h.symm)
    rw [leading_kernel] at hn
    exact ⟨s.val,List.mem_map.mpr ⟨r,by simp,rfl⟩,hn⟩
  | succ d ih =>
    obtain ⟨x,hx,hr⟩ := ih
    let r : gamma (d+2) := ⟨x⁻¹*g.val,hr⟩
    let v := (leading (d+1) r).toAdd
    obtain ⟨u,hu,hl⟩ := lift_by_power d v
    have he : leading (d+1) r = leading (d+1) u := by
      exact Multiplicative.toAdd.injective hl.symm
    have hn := (leading (d+1)).eq_iff.mp he
    rw [leading_kernel] at hn
    refine ⟨x*u.val, List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨u.val, ?_, rfl⟩⟩, ?_⟩
    · exact List.mem_map.mpr ⟨(liftBase 0 v).val, List.mem_map.mpr ⟨v,by simp,rfl⟩, hu.symm⟩
    · change u.val⁻¹*(x⁻¹*g.val) ∈ gamma (d+3) at hn
      simpa only [mul_inv_rev,mul_assoc] using hn

/-- Reduce an integral quaternion unit to the four coordinates at the given level. -/
def coordinates (l : ℕ) : Orderˣ →* Address l :=
  (reduce l).toMonoidHom.comp (Units.coeHom Order)

/-- The listing algorithm, reducing before any instance-dependent product is
taken. The two finite input tables are absolute constants. -/
noncomputable def listAddresses (d : ℕ) : List (Address (d+2)) :=
  expandDigits (firstTable.map (coordinates (d+2))) (digitTable.map (coordinates (d+2))) d

/-- All actual tile addresses occur in the output list. -/
theorem listAddresses_complete (d : ℕ) (t : Deck (d+2)) :
    ((deckAddress (d+2) t : (Address (d+2))ˣ) : Address (d+2)) ∈ listAddresses d := by
  classical
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ((gamma (d+2)).subgroupOf (gamma 1)) t
  obtain ⟨x,hx,hr⟩ := integral_list_complete d g
  have hm : x ∈ gamma 1 := by
    have ht := gamma_le_one (d+1) hr
    have hu := (gamma 1).mul_mem g.2 ((gamma 1).inv_mem ht)
    simpa using hu
  let y : gamma 1 := ⟨x,hm⟩
  have he : addressHom (d+2) g = addressHom (d+2) y := by
    apply (addressHom (d+2)).eq_iff.mpr
    rw [addressHom_ker]
    exact hr
  unfold listAddresses
  rw [← expand_map]
  exact List.mem_map.mpr ⟨x,hx,congrArg Units.val he.symm⟩

/-- The output list has exactly one entry per tile. -/
theorem listAddresses_length (d : ℕ) : (listAddresses d).length = tileCount (d+2) := by
  rw [listAddresses,expand_length,List.length_map,List.length_map,first_length,digit_length,
    tileCount_eq d,mul_comm]

end Cover

end BorderVNP
end Computability
end OAI
