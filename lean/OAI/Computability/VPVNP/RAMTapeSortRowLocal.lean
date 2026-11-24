import OAI.Computability.VPVNP.RAMTapeSortRowBranch

/-!
# The local branch of a physical sorting row

Both comparator operands are read from the current materialized array.
The next block receives the selected record and the validity register
receives its canonical-format check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open RAMBoundary Boundary

theorem program_local_runs {w B : ℕ} (s : Stacks Port) (block : Fin B → RawSlot w)
    (i j : Fin B) (keepMin : Bool) (h : Ready s block i j true keepMin) :
    ∃ t ≤ 4096*(B+1)*(w+1), program.Runs t s
      (result s keepMin (block i) (block j) none (s .crossSend) (s .crossReceive)) := by
  let t := Function.update s Port.localFlag []
  let a := block i
  let b := block j
  let u := Function.update t Port.left (recordBytes a)
  let v := Function.update u Port.right (recordBytes b)
  have ht : FetchReady w t := ⟨h.width, h.lookup, h.widthBack, h.saved, h.recordBack⟩
  have hu : FetchReady w u := ⟨h.width, h.lookup, h.widthBack, h.saved, h.recordBack⟩
  have h₁ : (fetch .first).Runs (5*i.val+2+SortGather.cost i.val w) t u := by
    have he := fetch_runs .first t block i ht h.block_eq h.row_eq
    change (fetch .first).Runs _ t (Function.update t .left (recordBytes a ++ t .left)) at he
    simpa only [show t .left = [] from h.left, List.append_nil] using he
  have h₂ : (fetch .other).Runs (5*j.val+2+SortGather.cost j.val w) u v := by
    have he := fetch_runs .other u block j hu h.block_eq h.partner_eq
    change (fetch .other).Runs _ u (Function.update u .right (recordBytes b ++ u .right)) at he
    simpa only [show u .right = [] from h.right, List.append_nil] using he
  have hcmp : CompareReady w v := ⟨h.width, h.widthBack, h.savedLeft, h.savedRight, h.selectTmp⟩
  have h₃ := oriented_runs .localRegister v keepMin a b [] [] hcmp h.orientation
    (by change recordBytes a = recordBytes a ++ []; rw [List.append_nil])
    (by change recordBytes b = recordBytes b ++ []; rw [List.append_nil])
  let out := result s keepMin a b none (s .crossSend) (s .crossReceive)
  have hpass := h₁.followedBy (h₂.followedBy h₃)
  have he : compareResult (Function.update v .orientation []) .localRegister [] []
      (recordBytes (chosen keepMin a b)).reverse (selectOK a b) =
      Function.update out .partner (s .partner) := by
    funext p
    cases p <;> first | rfl | exact h.left.symm | exact h.right.symm
  rw [he] at hpass
  have run := program_of_local h.localFlag hpass
  simp only [Function.update_self, Function.update_idem, h.partner_eq, List.length_replicate] at run
  have hclear : Function.update out Port.partner [] = out := by
    change Function.update out Port.partner (out .partner) = out
    exact Function.update_eq_self ..
  rw [hclear] at run
  have hc := rowCost_le (w := w) i.isLt.le j.isLt.le
  have hj := j.isLt
  exact ⟨_, by omega, run⟩

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
