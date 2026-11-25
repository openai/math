import OAI.Computability.BorderVNP.CoverLorentzIndex

/-!
# Modular addresses for quaternion tiles

A tile in the actual deck quotient is faithfully represented by the four
quaternion coordinates reduced modulo `7^l`. Right multiplication in the
quotient becomes multiplication of these four residues.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- Four quaternion coordinates modulo the level modulus. -/
abbrev Address (l : ℕ) := QuaternionAlgebra (ZMod (7^l)) 2 0 3

/-- Reduction of all four integral coordinates is a ring homomorphism. -/
def reduce (l : ℕ) : Order →+* Address l where
  toFun x := ⟨x.re,x.imI,x.imJ,x.imK⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    rcases x with ⟨a,b,c,d⟩
    rcases y with ⟨e,f,g,h⟩
    ext <;> simp [QuaternionAlgebra.mk_mul_mk]
    ring

private theorem reduce_sub_one (l : ℕ) (x : Order) :
    reduce l x = 1 ↔ ∃ y : Order, x = atDepth l y := by
  constructor
  · intro h
    have hn : reduce l (x-1) = 0 := by simp [map_sub,h]
    let v := x-1
    have div (f : Order → ℤ) (h : ((f v : ℤ) : ZMod (7^l)) = 0) : (7:ℤ)^l ∣ f v := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (f v) (7^l)).mp h
    obtain ⟨a,ha⟩ := div QuaternionAlgebra.re (congrArg QuaternionAlgebra.re hn)
    obtain ⟨b,hb⟩ := div QuaternionAlgebra.imI (congrArg QuaternionAlgebra.imI hn)
    obtain ⟨c,hc⟩ := div QuaternionAlgebra.imJ (congrArg QuaternionAlgebra.imJ hn)
    obtain ⟨d,hd⟩ := div QuaternionAlgebra.imK (congrArg QuaternionAlgebra.imK hn)
    let y : Order := ⟨a,b,c,d⟩
    have he : v = (7:ℤ)^l • y := QuaternionAlgebra.ext ha hb hc hd
    exact ⟨y, by change x = 1 + (7:ℤ)^l • y; rw [← he]; dsimp [v]; abel⟩
  · rintro ⟨y,rfl⟩
    have hz : (((7:ℤ)^l : ℤ) : ZMod (7^l)) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simp)
    rw [atDepth, map_add, map_one]
    suffices h : reduce l ((7:ℤ)^l • y) = 0 by rw [h,add_zero]
    ext <;> change (((7:ℤ)^l * _ : ℤ) : ZMod (7^l)) = 0 <;> rw [Int.cast_mul,hz,zero_mul]

/-- Modular multiplication acts on tile addresses, taking a norm-one
quaternion to a unit in the residue ring. -/
def addressHom (l : ℕ) : gamma 1 →* (Address l)ˣ :=
  (Units.map (reduce l).toMonoidHom).comp (gamma 1).subtype

/-- Two words have the same four-residue address precisely when they have
the same endpoint in the deck quotient. -/
theorem addressHom_ker (l : ℕ) :
    (addressHom l).ker = (gamma l).subgroupOf (gamma 1) := by
  ext x
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change reduce l x.val.val = 1 ↔ norm x.val.val = 1 ∧ ∃ y, x.val.val = atDepth l y
  rw [reduce_sub_one, and_iff_right x.2.1]

/-- The faithful representation of each deck group by modular quaternion units. -/
def deckAddress (l : ℕ) : Deck l →* (Address l)ˣ :=
  QuotientGroup.lift _ (addressHom l) (by rw [addressHom_ker])

/-- The four coordinates uniquely determine the tile. -/
theorem deckAddress_injective (l : ℕ) : Function.Injective (deckAddress l) := by
  intro x y h
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective ((gamma l).subgroupOf (gamma 1)) x
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective ((gamma l).subgroupOf (gamma 1)) y
  have he := (addressHom l).eq_iff.mp (show addressHom l a = addressHom l b from h)
  rw [addressHom_ker] at he
  apply (QuotientGroup.mk' _).eq_iff.mpr
  rwa [QuotientGroup.ker_mk']

end Cover

end BorderVNP
end Computability
end OAI
