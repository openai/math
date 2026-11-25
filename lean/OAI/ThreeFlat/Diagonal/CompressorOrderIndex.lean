import Mathlib.Data.Finset.Sort

namespace OAI
namespace ThreeFlat.Diagonal

/-- Rank in a finite sorted set is the cardinality of the strictly smaller elements. -/
theorem sorted_index {A : Type*} [LinearOrder A] {N : ℕ} (s : Finset A) (h : s.card = N) (i : Fin N) :
    (s.filter fun v => v < ((s.orderIsoOfFin h) i).val).card = i.val := by
  let e := s.orderIsoOfFin h
  let t := s.filter (fun v => v < (e i).val)
  let equiv : t ≃ Fin i.val := {
    toFun z := by
      have hz := Finset.mem_filter.mp z.property
      let v : s := ⟨z.val,hz.1⟩
      have lt : e.symm v < i := by
        apply e.lt_iff_lt.mp
        rw [e.apply_symm_apply]
        exact hz.2
      exact ⟨(e.symm v).val,lt⟩
    invFun j := by
      let a : Fin N := ⟨j.val,j.isLt.trans i.isLt⟩
      exact ⟨(e a).val,Finset.mem_filter.mpr ⟨(e a).property,
        e.strictMono (show a<i from j.isLt)⟩⟩
    left_inv z := by
      apply Subtype.ext
      exact congrArg (fun a : s => a.val) (e.apply_symm_apply ⟨z.val,(Finset.mem_filter.mp z.property).1⟩)
    right_inv j := by
      apply Fin.ext
      exact congrArg (fun a : Fin N => a.val) (e.symm_apply_apply ⟨j.val,j.isLt.trans i.isLt⟩) }
  exact (Fintype.card_coe t).symm.trans ((Fintype.card_congr equiv).trans (Fintype.card_fin _))

end ThreeFlat.Diagonal

end OAI
