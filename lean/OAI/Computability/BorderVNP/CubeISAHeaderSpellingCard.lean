import OAI.Computability.BorderVNP.CubeISAHeaderSpelling

/-! # Completeness of the compact cube broadcast representation

Sorting an unordered symbol pair supplies one upper-triangle row. Thus
the compact stream has exactly one bit position per broadcast bit, and
all raw streams of its fixed length correspond bijectively to raw broadcasts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.DeclarationBits

open RoutingISA RoutingISA.CubeLengths Physical Finset VPVNP.BurstRAM

variable {n d cap : ℕ}

/-- Dense indices in the upper triangle index exactly the unordered pairs
and all of their coordinate entries. -/
def upperEntries (d a : ℕ) : {k : Fin (d*d*a) // upper d a k.val} ≃ Sym2 (Fin d) × Fin a :=
  let group : {p : (Fin d × Fin d) × Fin a // p.1.1 ≤ p.1.2} ≃
      {st : Fin d × Fin d // st.1 ≤ st.2} × Fin a :=
    ⟨fun x => (⟨x.val.1,x.property⟩,x.val.2), fun x => ⟨(x.1.val,x.2),x.1.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  ((Equiv.subtypeEquiv (entryOrder d a).symm (fun k => upper_iff k)).trans group).trans
    (Sym2.sortEquiv.symm.prodCongr (Equiv.refl _))

private theorem fieldsBefore_sum (d a k : ℕ) :
    fieldsBefore d a k = ∑ j ∈ range k, if upper d a j then 1 else 0 := by
  induction k with
  | zero => simp [fieldsBefore]
  | succ k ih =>
    rw [fieldsBefore, sum_range_succ, ih]
    by_cases h : upper d a k <;> simp [h]

/-- There is one emitted field per cut for every unordered symbol pair, including diagonal pairs. -/
theorem fieldsBefore_last (d a : ℕ) :
    fieldsBefore d a (d*d*a) = Fintype.card (Sym2 (Fin d))*a := by
  rw [fieldsBefore_sum,← Fin.sum_univ_eq_sum_range]
  calc
    _ = (univ.filter fun k : Fin (d*d*a) => upper d a k.val).card := by simp
    _ = Fintype.card {k : Fin (d*d*a) // upper d a k.val} := (Fintype.card_subtype _).symm
    _ = _ := by simpa using Fintype.card_congr (upperEntries d a)

/-- Exact physical length, omitting unused square-table entries. -/
def length (n d cap : ℕ) : ℕ :=
  Nat.clog 2 (n+1) + Fintype.card (Sym2 (Fin d))*(n+1)*Nat.clog 2 (cap+1)

/-- Every raw broadcast uses the same physical length. -/
theorem spelling_length (f : Broadcast n d cap) : (spelling f).length = length n d cap := by
  simp [spelling,length,length_rowBits f _ le_rfl,fieldsBefore_last]

private theorem pack_flat (xs : List Bool) :
    TeamContraction.JointHeader.FlatAt (w := 1)
      (fun j => DiagonalResidueRAM.word 1 (xs[j]?.getD false).toNat) 0 xs := by
  intro i
  simp

/-- Equality of the compact input words recovers every raw bit of the original
broadcast, regardless of whether its encoded integers are in range. -/
theorem spelling_injective : Function.Injective (spelling (n := n) (d := d) (cap := cap)) := by
  intro f g eqn
  let m : Memory 1 := fun j => DiagonalResidueRAM.word 1 ((spelling f)[j]?.getD false).toNat
  have hf : TeamContraction.JointHeader.FlatAt m 0 (spelling f) := pack_flat _
  have hg : TeamContraction.JointHeader.FlatAt m 0 (spelling g) := eqn ▸ hf
  have bi : Function.Injective Bool.toNat := by decide
  apply Prod.ext
  · funext j
    exact bi (((coordinate_bits (by decide) hf j).symm).trans (coordinate_bits (by decide) hg j))
  · funext pair j bit
    let st := Sym2.sortEquiv pair
    let k := entryOrder d (n+1) (st.val,j)
    have hu : upper d (n+1) k.val := (upper_iff _).mpr (by simpa only [k,Equiv.symm_apply_apply] using st.property)
    have ef : field f k = f.2 pair j := by
      simp only [field,k,Equiv.symm_apply_apply]
      rw [show Sym2.mk st.val.1 st.val.2 = pair from Sym2.sortEquiv.symm_apply_apply pair]
    have eg : field g k = g.2 pair j := by
      simp only [field,k,Equiv.symm_apply_apply]
      rw [show Sym2.mk st.val.1 st.val.2 = pair from Sym2.sortEquiv.symm_apply_apply pair]
    have h := ((row_bits (by decide) hf k hu bit).symm).trans (row_bits (by decide) hg k hu bit)
    rw [ef,eg] at h
    exact bi h

/-- The compact spelling as a fixed-width physical Boolean bank. -/
def spellingWord (f : Broadcast n d cap) (j : Fin (length n d cap)) : Bool :=
  (spelling f)[j.val]'(by simpa only [spelling_length] using j.isLt)

/-- Raw broadcasts and fixed-length header segments correspond in both directions.
Consequently the compact encoding introduces no additional guessed bits. -/
noncomputable def wordEquiv (n d cap : ℕ) : Broadcast n d cap ≃ (Fin (length n d cap) → Bool) := by
  let e := spellingWord (n := n) (d := d) (cap := cap)
  apply Equiv.ofBijective e
  apply (Fintype.bijective_iff_injective_and_card e).mpr
  constructor
  · intro f g he
    apply spelling_injective
    apply List.ext_getElem (by simp [spelling_length])
    intro i hi _
    exact congrFun he ⟨i, by simpa only [spelling_length] using hi⟩
  · classical
    have dom : Fintype.card (Broadcast n d cap) =
        2^(Nat.clog 2 (n+1)) * (2^(Nat.clog 2 (cap+1)*(n+1)*Fintype.card (Sym2 (Fin d)))) := by
      simp only [Broadcast,Physical.Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
        Fintype.card_bool,← pow_mul]
    have cod : Fintype.card (Fin (length n d cap) → Bool) = 2^(length n d cap) := by simp
    rw [dom,cod,length,pow_add]
    congr 2
    ac_rfl

end Cube.DeclarationBits

end BorderVNP
end Computability
end OAI
