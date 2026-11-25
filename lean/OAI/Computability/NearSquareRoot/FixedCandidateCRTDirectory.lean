import OAI.Computability.NearSquareRoot.FixedCandidateCRTDispatch
import OAI.Computability.NearSquareRoot.CRTTableNativePlanSpec

/-! # The complete physical batch directory generated from each CRT stage seed -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTDispatch
open IntegerMultiplication Code Staff Strip Carry Controlled CRTTable

abbrev Cap (k : ℕ) := blocksPerBatch k 4 (CRTBudget.stride k)

private def metric (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem units {X : Type} [Codec X] (f : X → Tally) (p : Poly f) :
    Realizes (metric X) (fun x => (f x).length) := by
  change Poly (fun x : X => tally (f x).length)
  simpa only [recover_tally] using p

theorem guard_poly : Poly (fun t : Tally => tally (guardWidth t.length)) := by
  have N := units id (Code.Poly.identity (X := Tally))
  have log := (Figure.of_spoken (N.plus (.fix 1))).short_log
  exact (Realizes.fix 7).plus ((Realizes.fix 2).times log)

theorem cap_poly : Poly (fun t : Tally => tally (Cap t.length)) := by
  have N := units id (Code.Poly.identity (X := Tally))
  have G : Realizes (metric Tally) (fun t => guardWidth t.length) := guard_poly
  have W : Realizes (metric Tally) (fun t => BoxScale.width t.length) := BoxParameterTask.width_poly
  have stride := G.plus (W.minused G)
  have cap := N.dividing ((Realizes.fix (8*4)).times stride)
  change Realizes (metric Tally) (fun t => Cap t.length)
  have hm (k : ℕ) : guardWidth k + (BoxScale.width k - guardWidth k) = CRTBudget.stride k := by
    unfold CRTBudget.stride; omega
  change Realizes (metric Tally) (fun t => t.length/(8*4*CRTBudget.stride t.length))
  simpa only [id_eq,hm] using cap

/-- Read the actual address width by concatenating the unary axis width rulers. -/
def bits (s : HeaderSeed) : Tally := (s.2.2.2.map Prod.fst).flatten

theorem bits_easy : Easy bits :=
  ((show Easy (fun s : HeaderSeed => s.2.2.2) by fun_prop).compose Easy.fst.mapping).compose Easy.flatten

/-- Every target ordinal appears, even if its current Beneš stage is inactive. -/
def widths (s : HeaderSeed) : List Tally := (stageHeader s).2.map (fun b => b.2.1)

theorem widths_poly : Poly widths :=
  (stageHeader_poly.compose Easy.snd.poly).compose
    (Poly.maps _ (show Poly (fun b : Benes.BlockPlan TargetTag => b.2.1) by fun_prop))

def batchN (s : HeaderSeed) := s.2.2.2.length ⌈/⌉ Cap (bits s).length

theorem batchN_poly : Poly (fun s : HeaderSeed => tally (batchN s)) := by
  have N := units (fun s : HeaderSeed => ruler s.2.2.2) ((Easy.ruler (by fun_prop)).poly)
  have C : Realizes (metric HeaderSeed) (fun s => Cap (bits s).length) := bits_easy.poly.compose cap_poly
  have h := ((N.plus C).minused (Realizes.fix 1)).dividing C
  change Realizes (metric HeaderSeed) (fun s => (s.2.2.2.length+Cap (bits s).length-1)/Cap (bits s).length)
  simpa only [ruler_length] using h

/-- Native input includes the reserve, guard, address width and actual list of
active target ordinals for this contiguous physical group. -/
def issue (low : Tally → Tally) (p : HeaderSeed × Tally) : Native.Seed :=
  let k := bits p.1
  (p.1,(low k,tally (guardWidth k.length)),k,
    activeIDs ((tally (Cap k.length),p.2,p.1.1.2),widths p.1))

theorem issue_poly (low : Tally → Tally) (pl : Poly low) : Poly (issue low) := by
  let X := HeaderSeed × Tally
  have k := (Easy.fst (X := HeaderSeed) (Y := Tally)).compose bits_easy
  have heads := (k.poly.compose pl).pair (k.poly.compose guard_poly)
  have key := (k.poly.compose cap_poly).pair ((Easy.snd (X := HeaderSeed) (Y := Tally)).poly.pair
    (show Poly (fun p : X => p.1.1.2) by fun_prop))
  have ids := (key.pair (Easy.fst.poly.compose widths_poly)).compose activeIDs_poly
  exact Easy.fst.poly.pair (heads.pair (k.poly.pair ids))

def directory (low : Tally → Tally) (s : HeaderSeed) : List Native.Seed :=
  polyPush (issue low) (s,Iter.lineup (tally (batchN s)))

theorem directory_poly (low : Tally → Tally) (pl : Poly low) : Poly (directory low) :=
  (Code.Poly.identity.pair (batchN_poly.compose Iter.poly_line)).compose (Poly.push default [] (issue_poly low pl))

theorem directory_eq (low : Tally → Tally) (s : HeaderSeed) :
    directory low s = List.ofFn (fun i : Fin (batchN s) => issue low (s,tally i.val)) := by
  simp [directory,Iter.lined,polyPush,Function.comp_def]

theorem box_encoded (box : List (ℕ × ℕ)) :
    (box.map fun p => (tally p.1,tally p.2)) =
      (List.finRange box.length).map (descriptor (BoxFin.modulus box) (axisWidth box)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [descriptor,BoxFin.modulus,axisWidth]

variable {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box) {d : ℕ}
abbrev row (side : Bool) (j : ℕ) (inv : Bool) (depth : ℕ) (box : List (ℕ × ℕ)) : HeaderSeed :=
  ((side,tally j),inv,tally depth,(List.finRange box.length).map (descriptor (BoxFin.modulus box) (axisWidth box)))

include hb in
theorem bits_row (side : Bool) (j : ℕ) (inv : Bool) (depth : ℕ) :
    bits (row side j inv depth box) = tally k := by
  rw [← recover_tally (bits _)]
  congr 1
  simp [bits,descriptor,Function.comp_def,List.length_flatten,← List.ofFn_eq_map,
    List.map_ofFn,List.sum_ofFn,Native.total hb]

noncomputable abbrev targetWidth (box : List (ℕ × ℕ)) (depth : ℕ) (b : Fin (targetOrder box.length depth).length) :=
  axisWidth box (targetAxis box.length depth (targetRank box.length depth b))

theorem widths_row (side : Bool) (j : ℕ) (inv : Bool) (depth : ℕ) (hd : depth ≤ Nat.clog 2 box.length) :
    widths (row side j inv depth box) = List.ofFn (fun b => tally (targetWidth box depth b)) := by
  rw [widths,row,stageHeader_makePlan _ _ depth hd]
  simp [Benes.makePlan,Function.comp_def,targetWidth]

include hb in
theorem actual_issue (side inv : Bool) (depth j β : ℕ) (hd : depth ≤ Nat.clog 2 box.length)
    (low : Tally → Tally) :
    issue low (row side j inv depth box,tally β) = Native.seed
      (k := k) (selectBlock (Cap k) β j (targetWidth box depth)) side inv j (guardWidth k) (low (tally k)).length := by
  simp only [issue,bits_row hb,tally_length,widths_row side j inv depth hd,activeIDs_ofFn]
  simp [Native.seed,row,recover_tally]

include hb in
theorem batch_count (side inv : Bool) (depth j : ℕ) :
    batchN (row side j inv depth box) = batchCount box.length k 4 (CRTBudget.stride k) := by
  simp [batchN,bits_row hb,row,batchCount]

end FixedCandidate.CRTDispatch

end NearSquareRoot
end Computability
end OAI
