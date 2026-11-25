import OAI.Hierarchy.DescentGLTransitive
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis

namespace OAI
/-! # Independent rows are exactly the extendible prefixes of binary layouts -/

namespace Hierarchy.DescentGL
open scoped Classical
noncomputable section

private abbrev BitSpace (k : ℕ) := Fin k → ZMod 2
private abbrev BinaryLayout (k : ℕ) := BitSpace k ≃ₗ[ZMod 2] BitSpace k

abbrev Row (k : ℕ) := Module.Dual (ZMod 2) (BitSpace k)

private def coordinateBasis (k : ℕ) : Module.Basis (Fin k) (ZMod 2) (Row k) :=
  (Pi.basisFun (ZMod 2) (Fin k)).dualBasis

/-- An output bit as a linear functional on the input bits. -/
def rowFunctional {k : ℕ} (L : BinaryLayout k) (i : Fin k) : Row k :=
  L.dualMap (coordinateBasis k i)

@[simp] theorem rowFunctional_apply {k : ℕ} (L : BinaryLayout k) (i : Fin k) (x : BitSpace k) :
    rowFunctional L i x=L x i := by
  change (Pi.basisFun (ZMod 2) (Fin k)).dualBasis i (L x)=_
  rw [Module.Basis.dualBasis_apply,Pi.basisFun_repr]

/-- Every ordered independent family of binary linear functionals is already
the beginning of some actual invertible layout. -/
theorem feasible_rows_iff {h k : ℕ} (hk : h≤k) (rows : Fin h → Row k) :
    (∃ L : BinaryLayout k, ∀ i, rowFunctional L (i.castLE hk)=rows i) ↔
      LinearIndependent (ZMod 2) rows := by
  let C := coordinateBasis k
  let pick := fun i : Fin h => i.castLE hk
  have inj : Function.Injective pick := fun _ _ eqn => Fin.ext (congrArg (fun z : Fin k => z.val) eqn)
  have hc := C.linearIndependent.comp pick inj
  constructor
  · rintro ⟨L, matchRows⟩
    have copy : (fun i => C.map L.dualMap (pick i))=rows := funext matchRows
    rw [←copy]
    exact (C.map L.dualMap).linearIndependent.comp pick inj
  · intro independent
    let left := hc.linearCombinationEquiv
    let right := independent.linearCombinationEquiv
    obtain ⟨T,hT⟩ := Submodule.exists_linearEquiv_restrict_eq (left.symm.trans right)
    have acts (i : Fin h) : T (C (pick i))=rows i := by
      let δ : Fin h →₀ ZMod 2 := Finsupp.single i 1
      have e := hT (left δ)
      change (right (left.symm (left δ))).val=T (left δ).val at e
      rw [left.symm_apply_apply] at e
      simpa [left, right, δ, Finsupp.linearCombination_single] using e.symm
    let B := C.map T
    let ev := Module.evalEquiv (ZMod 2) (BitSpace k)
    let L : BinaryLayout k := ev.trans B.dualBasis.equivFun
    refine ⟨L,fun i => ?_⟩
    apply LinearMap.ext
    intro x
    rw [rowFunctional_apply]
    change B.dualBasis.equivFun (ev x) (pick i)=_
    rw [Module.Basis.dualBasis_equivFun]
    change T (C (pick i)) x=rows i x
    rw [acts]

/-- At the next step, feasibility is precisely exclusion from the span of the
already fixed rows. Both the prefix and the new row are realized by one GL matrix. -/
theorem feasible_next_row_iff {h k : ℕ} (hk : h<k) (base : BinaryLayout k) (candidate : Row k) :
    (∃ L : BinaryLayout k,
      (∀ i : Fin h, rowFunctional L (i.castLE hk.le)=rowFunctional base (i.castLE hk.le)) ∧
      rowFunctional L ⟨h,hk⟩=candidate) ↔
      candidate ∉ Submodule.span (ZMod 2) (Set.range fun i : Fin h => rowFunctional base (i.castLE hk.le)) := by
  let rows := fun i : Fin h => rowFunctional base (i.castLE hk.le)
  have indep := (feasible_rows_iff hk.le rows).mp ⟨base,fun _ => rfl⟩
  have full := feasible_rows_iff (Nat.succ_le_of_lt hk) (Fin.snoc rows candidate)
  rw [linearIndependent_finSnoc] at full
  have lastIdx : (Fin.last h).castLE (Nat.succ_le_of_lt hk)=⟨h,hk⟩ := Fin.ext rfl
  have oldIdx (i : Fin h) : i.castSucc.castLE (Nat.succ_le_of_lt hk)=i.castLE hk.le := Fin.ext rfl
  constructor
  · rintro ⟨L,prev,last⟩
    apply (full.mp ?_).2
    refine ⟨L,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, lastIdx] using last
    · simpa only [Fin.snoc_castSucc, oldIdx, rows] using prev j
  · intro outside
    obtain ⟨L,allRows⟩ := full.mpr ⟨indep,outside⟩
    refine ⟨L,fun i => ?_,?_⟩
    · simpa only [Fin.snoc_castSucc, oldIdx, rows] using allRows i.castSucc
    · simpa only [Fin.snoc_last, lastIdx] using allRows (Fin.last h)


end
end Hierarchy.DescentGL

end OAI
