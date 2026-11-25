import OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
import OAI.Computability.MultitapeWeakETH.ChildPackets

/-! # Reading the ordered hidden fields of one shrinking site on bit tapes -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkHidden

open IntegerMultiplication Code VPVNP BurstRAM PairSimulation ShrinkHiddenGuess
open CompressorRecords PhaseRecipe NativeGrid TerminalWords
open scoped Fin.CommRing
noncomputable section

variable {A : Type} [Codec A] [Inhabited A] (read : A × Bits.Word → Bits.Word)

/-- Read the dense ID and actual selected width of every field in directory order.
The row stride bounds the count and the supplied unary cap bounds each decoded width. -/
theorem scan_program (hr : Poly read) (stride selectors : ℕ) :
    ∃ scan : Query A → List (Bits.Word × Tally), Poly scan ∧ ∀ {w : ℕ} (ctx : A)
      (head cap : ℕ) (m : Memory w) (g : Args w) (rows : List Row),
      (∀ j : Word w, read (ctx,wordBits j) = wordBits (m j.val)) →
      Header.Published g head m → head+38 < 2^w → g.selectorBits = (selectors : Word w) →
      g.rowStride = stride → g.countBase+g.owner < 2^w →
      (m (g.countBase+g.owner)).val = rows.length → rows.length ≤ stride →
      ValidRows g m rows → (∀ e ∈ rows, e.2.length ≤ cap) →
      scan (query ctx (head : Word w) cap g.owner) =
        rows.map (fun e => (wordBits (e.1 : Word w),tally e.2.length)) := by
  choose eval cost correct using expression read hr
  let count (q : Query A) := capped (eval countExpr (q,[]),tally stride)
  let field (q : Indexed A) := (eval (idExpr stride) q,capped (eval (widthExpr stride selectors) q,q.1.1.2))
  have cp : Poly count := (((Poly.identity.pair (Code.Poly.const ([] : Tally))).compose (cost countExpr)).pair
    (Code.Poly.const (tally stride))).compose capped_poly
  have fp : Poly field := (cost (idExpr stride)).pair (((cost (widthExpr stride selectors)).pair
    (show Poly (fun q : Indexed A => q.1.1.2) by fun_prop)).compose capped_poly)
  refine ⟨fun q => (Iter.lineup (count q)).map fun j => field (q,j),
    (Poly.identity.pair (cp.compose Iter.poly_line)).compose (Poly.push default [] fp),?_⟩
  intro w ctx head cap m g rows rd pub room sel pitch fits len limited valid bound
  let q := query ctx (head : Word w) cap g.owner
  have countOk : count q = tally rows.length := by
    have eqn := correct countExpr ctx (head : Word w) cap g.owner 0 m rd
    have h := (recipe_readback g head 0 selectors m pub room sel fits).1
    change tally (min (Bits.value (eval countExpr (q,tally 0))) (tally stride).length) = _
    rw [eqn.trans (congrArg wordBits h),value_native,len,tally_length,Nat.min_eq_left limited]
  have one (i : Fin rows.length) : field (q,tally i.val) =
      (wordBits (rows[i.val].1 : Word w),tally rows[i.val].2.length) := by
    obtain ⟨_,id,width⟩ := recipe_readback g head i.val selectors m pub room sel fits
    rw [pitch] at id width
    have entry := valid i
    let key := m (((g.row+i.val : ℕ) : Word w).val)
    change key.val = _ ∧ (g.width m key).val = _ ∧ _ at entry
    have word : key = (rows[i.val].1 : Word w) := entry.1 ▸ (Fin.cast_val_eq_self _).symm
    have idCode := (correct (idExpr stride) ctx (head : Word w) cap g.owner i.val m rd).trans (congrArg wordBits id)
    have widthCode := (correct (widthExpr stride selectors) ctx (head : Word w) cap g.owner i.val m rd).trans (congrArg wordBits width)
    refine Prod.ext (idCode.trans (congrArg wordBits word)) (congrArg tally ?_)
    change min (Bits.value (eval (widthExpr stride selectors) (query ctx _ cap g.owner,tally i.val))) (tally cap).length = _
    rw [widthCode,value_native,tally_length]
    change min (g.width m key).val cap = _
    rw [entry.2.1,Nat.min_eq_left (bound _ (List.getElem_mem i.isLt))]
  change (Iter.lineup (count q)).map _ = _
  rw [countOk,Iter.lined,List.map_ofFn]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simpa only [List.getElem_ofFn,List.getElem_map,Function.comp_apply] using one ⟨i,by simpa using hi⟩

end
end OAI.Computability.MultitapeWeakETH.ShrinkHidden
