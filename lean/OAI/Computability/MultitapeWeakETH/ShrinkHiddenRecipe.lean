import OAI.Computability.MultitapeWeakETH.HistoryField
import OAI.Computability.MultitapeWeakETH.WordExpression
import OAI.Computability.VPVNP.PairShrinkHiddenInputs

/-! # Recovering the ID and bit width of an absorbed shrinking field -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkHidden

open IntegerMultiplication Code Carry Staff Strip VPVNP BurstRAM BurstRAM.PrivateRAM CompressorRecords
open PairSimulation ShrinkHiddenGuess PhaseRecipe NativeGrid
open private encoded_short from OAI.Computability.MultitapeWeakETH.TerminalLayout
open scoped Fin.CommRing
noncomputable section

/-- Word zero names the owner and word one indexes the owner's row. -/
def countExpr : Expr := .load ((Expr.header 31).add (.publicWord 0))

def idExpr (stride : ℕ) : Expr :=
  .load (((Expr.header 32).add ((Expr.publicWord 0).mul (.lit stride))).add (.publicWord 1))

def widthExpr (stride selectors : ℕ) : Expr :=
  let id := idExpr stride
  let base := (Expr.header 36).add ((id.div (.lit 4)).mul (.header 37))
  let coord := (((Expr.lit 1).sub (.header 38)).mul (.lit 4)).add (id.mod (.lit 4))
  (Expr.load ((base.add (.lit 2)).add coord)).add
    ((Expr.load (base.add (.lit 1))).mul (.lit selectors))

private def publicWords {w : ℕ} (site index : ℕ) (j : Fin 5) : Word w :=
  if j = 0 then (site : Word w) else (index : Word w)

theorem recipe_readback {w : ℕ} (g : Args w) (head index selectors : ℕ) (m : Memory w)
    (header : Header.Published g head m) (room : head+38 < 2^w)
    (sel : g.selectorBits = (selectors : Word w)) (countFits : g.countBase + g.owner < 2^w) :
    let ev := fun e : Expr => e.eval (publicWords g.owner index) (head : Word w) m
    let id := m (((g.row + index : ℕ) : Word w).val)
    ev countExpr = m (g.countBase + g.owner) ∧ ev (idExpr g.rowStride) = id ∧
      ev (widthExpr g.rowStride selectors) = g.width m id := by
  intro ev id
  have h (j : ℕ) (hj : j ≤ 38) : ev (.header j) = m (head+j) := by
    change m (((head : Word w) + (j : Word w)).val) = _
    rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have owner : ev (.publicWord 0) = (g.owner : Word w) := rfl
  have ordinal : ev (.publicWord 1) = (index : Word w) := rfl
  have idx : ev (idExpr g.rowStride) = id := by
    change m (ev (.header 32) + ev (.publicWord 0) * (g.rowStride : Word w) + ev (.publicWord 1)).val = _
    rw [h 32 (by decide),header.rows,owner,ordinal]
    simp only [id,Args.row,Nat.cast_add,Nat.cast_mul]
  refine ⟨?_,idx,?_⟩
  · change m (ev (.header 31) + ev (.publicWord 0)).val = _
    rw [h 31 (by decide),header.counts,owner,← Nat.cast_add,Fin.val_cast_of_lt countFits]
  · let base := ev (.header 36) + BinaryOp.div.eval (ev (idExpr g.rowStride)) 4 * ev (.header 37)
    let coord := (1 - ev (.header 38)) * 4 + BinaryOp.mod.eval (ev (idExpr g.rowStride)) 4
    change m (base+2+coord).val + m (base+1).val * (selectors : Word w) = _
    dsimp only [base,coord]
    rw [idx,h 36 (by decide),header.term,h 37 (by decide),header.stride,h 38 (by decide),header.layout,← sel]
    rfl

private abbrev regime (X : Type) [Codec X] : Regime X := ⟨size,send,Dom.base _⟩
private def ordinalWord (q : Bits.Word × Tally) := Bits.short q.1.length q.2.length

private theorem ordinalWord_poly : Poly ordinalWord := by
  let ρ := regime (Bits.Word × Tally)
  have w : Realizes ρ (fun q => q.1.length) := by
    change Poly (fun q : Bits.Word × Tally => tally q.1.length)
    convert (Easy.ruler (Easy.fst (X:=Bits.Word) (Y:=Tally))).poly using 1
    funext q
    rw [← ruler_length q.1,recover_tally]
  have val : Realizes ρ (fun q => q.2.length) := by
    change Poly (fun q : Bits.Word × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Bits.Word) (Y:=Tally)).poly
  exact (Figure.of_spoken val).write w

abbrev Query (A : Type) := ChildScan.Query A
abbrev Indexed (A : Type) := Query A × Tally

def query {A : Type} {w : ℕ} (ctx : A) (head : Word w) (cap owner : ℕ) : Query A :=
  (((ctx,wordBits head),tally cap),tally owner)

variable {A : Type} [Codec A] (read : A × Bits.Word → Bits.Word)

theorem expression (hr : Poly read) (e : Expr) :
    ∃ run : Indexed A → Bits.Word, Poly run ∧ ∀ {w : ℕ} (ctx : A) (head : Word w)
      (cap owner index : ℕ) (m : Memory w), (∀ j : Word w, read (ctx,wordBits j) = wordBits (m j.val)) →
      run (query ctx head cap owner,tally index) = wordBits (e.eval (publicWords owner index) head m) := by
  let head (x : Indexed A) := x.1.1.1.2
  let pub (j : Fin 5) (x : Indexed A) := ordinalWord (head x,if j=0 then x.1.2 else x.2)
  let mem (x : Indexed A × Bits.Word) := read (x.1.1.1.1.1,x.2)
  have hp : Poly head := by unfold head; fun_prop
  have pp (j : Fin 5) : Poly (pub j) := by
    by_cases hz : j=0
    · simpa only [pub,ite_eq_left hz] using (hp.pair (Easy.fst.compose Easy.snd).poly).compose ordinalWord_poly
    · simpa only [pub,ite_eq_right hz] using (hp.pair Easy.snd.poly).compose ordinalWord_poly
  have mp : Poly mem := (show Poly (fun x : Indexed A × Bits.Word => (x.1.1.1.1.1,x.2)) by fun_prop).compose hr
  obtain ⟨run,cost,ev⟩ := WordExpression.expression_program e pub head mem pp hp mp
  refine ⟨run,cost,?_⟩
  intro w ctx ptr cap owner index m rd
  apply ev _ _ ptr m _ rfl rd
  intro j
  by_cases hz : j=0 <;>
    simp only [pub,head,query,ordinalWord,length_wordBits,publicWords,hz,ite_true,ite_false,tally_length] <;>
    exact (encoded_short _ _).symm

end
end OAI.Computability.MultitapeWeakETH.ShrinkHidden
