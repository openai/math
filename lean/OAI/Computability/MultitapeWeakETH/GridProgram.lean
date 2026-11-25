import OAI.Computability.MultitapeWeakETH.AddressProgram
import OAI.Computability.MultitapeWeakETH.VolumeGrid
import OAI.Computability.NearSquareRoot.CRTTablePadded

/-! # Preparing the full Beneš table from the volume and the formula -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram

open Algorithms.SubexponentialSAT IntegerMultiplication IntegerMultiplication.Code
open IntegerMultiplication.Staff IntegerMultiplication.Strip IntegerMultiplication.Carry
open NearSquareRoot NearSquareRoot.Benes FormulaRanks DyadicBudget
open scoped Classical
noncomputable section

private abbrev regime : Regime Tally := ⟨size,send,Dom.base _⟩

private theorem volume_read : Realizes regime List.length := by
  change Poly (fun x : Tally => tally x.length)
  simp only [recover_tally]
  exact Code.Poly.identity

/-- Computing the base-2^b ceiling logarithm requires only ordinary binary
logarithm and division by the fixed block size. -/
theorem index_program (b : ℕ) : Realizes regime (fun x => index b x.length) := by
  let L := (Figure.of_spoken volume_read).short_log
  let A := L.plus (Realizes.fix (b-1))
  have q := (Figure.of_spoken A).quotients (Figure.natural b)
  simp only [index,Nat.clog_pow_left]
  exact q.pay ((diameter _ A).mono fun x => Nat.div_le_self _ _)

def siteWidth (b : ℕ) (N : Tally) := tally (b*index b N.length)

theorem siteWidth_poly (b : ℕ) : Poly (siteWidth b) :=
  (Realizes.fix b).times (index_program b)

private def capHint (b : ℕ) (N : Tally) := tally (2^(b+2)*(N.length+1))

private theorem capHint_poly (b : ℕ) : Poly (capHint b) :=
  (Realizes.fix (2^(b+2))).times (volume_read.plus (Realizes.fix 1))

private def widthWithPorts (k : Tally) := () :: () :: k
private theorem widthWithPorts_poly : Poly widthWithPorts := by unfold widthWithPorts; fun_prop

private def allFields (q : Tally × Tally) :=
  (Iter.lineup (CRTTable.padded q)).map fun i => field (q.1,i)

private theorem allFields_poly : Poly allFields :=
  (Easy.fst.poly.pair (CRTTable.padded_poly.compose Iter.poly_line)).compose (Poly.push [] [] field_poly)

private theorem allFields_eq (d h : ℕ) (fit : 2^d ≤ 2*h) :
    allFields (tally d,tally h) =
      (List.ofFn (VPVNP.RAMSerialization.wordBits d)).map List.ofFn := by
  simp only [allFields,CRTTable.padded,tally_length,min_eq_left fit,Iter.lined,List.map_ofFn,Function.comp_def]
  exact congrArg List.ofFn (funext (field_eq d))

abbrev VolumeInput := Tally × Input

def prepare (b : ℕ) (q : VolumeInput) : RawTable :=
  let k := siteWidth b q.1
  filledTable (rows (k,q.2),allFields (widthWithPorts k,capHint b q.1))

attribute [local irreducible] rows filledTable allFields capHint siteWidth widthWithPorts

theorem prepare_poly (b : ℕ) : Poly (prepare b) := by
  unfold prepare
  have k : Poly (fun q : VolumeInput => siteWidth b q.1) :=
    Easy.fst.poly.compose (siteWidth_poly b)
  have rp : Poly (fun q : VolumeInput => rows (siteWidth b q.1,q.2)) :=
    (k.pair Easy.snd.poly).compose rows_poly
  have keys : Poly (fun q : VolumeInput => allFields (widthWithPorts (siteWidth b q.1),capHint b q.1)) :=
    ((k.compose widthWithPorts_poly).pair (Easy.fst.poly.compose (capHint_poly b))).compose allFields_poly
  exact (rp.pair keys).compose filledTable_poly

set_option maxHeartbeats 1200000 in
theorem prepare_represents {n b N : ℕ} (hb : 0 < b) (hN : 1 < N) (F : SAT.CNF (Fin n))
    (wd : SAT.WidthAtMost 3 F) (fit : Fintype.card (Site F) ≤ 2^(b*index b N)) :
    RawRepresents (exchange F fit wd)
      (prepare b (tally N,tally n,(Encoding.cnfNumbers F).map encodeKey)) := by
  let k := b*index b N
  have bound := (grid_cover hb hN).2
  have cap : 2^(k+2) ≤ 2*(2^(b+2)*(N+1)) := by
    dsimp [k]
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  simp only [prepare,siteWidth,capHint,tally_length,widthWithPorts,← tally_succ]
  change RawRepresents _ (filledTable (rows (tally k,_,_),allFields (tally (k+2),tally (2^(b+2)*(N+1)))))
  obtain ⟨es,all,h⟩ := rows_eq F wd fit
  rw [h,allFields_eq (k+2) _ cap]
  let num := VPVNP.RAMSerialization.wordBits (k+2)
  exact filledTable_represents F fit wd es all (List.ofFn num) (List.nodup_ofFn.mpr num.injective)
    (fun x => List.mem_ofFn.mpr (num.surjective x))

theorem prepare_at_width {n b N k : ℕ} (hb : 0 < b) (hN : 1 < N) (hk : k = b*index b N)
    (F : SAT.CNF (Fin n)) (wd : SAT.WidthAtMost 3 F) (fit : Fintype.card (Site F) ≤ 2^k) :
    RawRepresents (exchange F fit wd) (prepare b (tally N,tally n,(Encoding.cnfNumbers F).map encodeKey)) := by
  subst k
  exact prepare_represents hb hN F wd fit

theorem switches_poly (b : ℕ) : Poly (fun q : VolumeInput =>
    generateTables (widthWithPorts (siteWidth b q.1),prepare b q)) :=
  (((Easy.fst.poly.compose (siteWidth_poly b)).compose widthWithPorts_poly).pair (prepare_poly b)).compose generateTables_poly

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SyntaxProgram
