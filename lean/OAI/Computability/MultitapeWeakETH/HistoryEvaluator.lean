import OAI.Computability.MultitapeWeakETH.GuardedHistory
import OAI.Computability.MultitapeWeakETH.HistoryCutoffs

/-! # Executing the full private site reader on bit tapes -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory
open NodeArguments WitnessWalk DyadicBudget NetworkKernel
open scoped Classical
noncomputable section

abbrev PrivateQuery := (VisitContext × Job) × Bits.Word

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates) (hist : ℕ)

private def cap (ctx : VisitContext) (bits : Bits.Word) : ℕ :=
  ((visitRoom B ctx).length+1)*visitFuel B ctx.1.1.length + 2*bits.length + (2*hist+2)*ctx.1.1.length + 5

def siteEval (visit : Visit VisitContext) (q : PrivateQuery) : Option (Bits.Word × List Tally) :=
  let ctx := q.1.1
  evaluate visit (tally (visitFuel B ctx.1.1.length),(ctx,tally (cap B hist ctx q.2)),some (([q.1.2],q.2),[]))

private abbrev reg := (⟨size,send,Dom.base _⟩ : Strip.Regime PrivateQuery)

private theorem fixed_pow {f : PrivateQuery → ℕ} (input : Staff.Realizes reg f) (d : ℕ) :
    Staff.Realizes reg (fun q => f q ^ d) := by
  induction d with
  | zero => exact (by simpa only [pow_zero] using Staff.Realizes.fix (r:=reg) 1)
  | succ d ih => simpa only [pow_succ] using ih.times input

theorem siteEval_poly {visit : Visit VisitContext} (h : Poly visit) : Poly (siteEval B hist visit) := by
  have vol : Staff.Realizes reg (fun q => q.1.1.1.1.length) := by
    change Poly (fun q : PrivateQuery => tally q.1.1.1.1.length)
    simpa only [recover_tally] using (show Poly (fun q : PrivateQuery => q.1.1.1.1) by fun_prop)
  have fuel : Staff.Realizes reg (fun q => visitFuel B q.1.1.1.1.length) :=
    fixed_pow ((Staff.Realizes.fix (2^(4*stepSize B))).times vol) _
  have ctx : Poly (fun q : PrivateQuery => q.1.1) := by fun_prop
  have room : Staff.Realizes reg (fun q => (visitRoom B q.1.1).length) := by
    change Poly (fun q : PrivateQuery => tally (visitRoom B q.1.1).length)
    simpa only [recover_tally] using ctx.compose (visitRoom_poly B)
  have len : Staff.Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : PrivateQuery => tally q.2.length)
    convert (Easy.ruler (Easy.snd (X:=VisitContext × Job) (Y:=Bits.Word))).poly using 1
    funext q
    rw [← ruler_length q.2,recover_tally]
  have bound : Staff.Realizes reg (fun q => cap B hist q.1.1 q.2) :=
    (((((room.plus (.fix 1)).times fuel).plus ((Staff.Realizes.fix 2).times len)).plus
      ((Staff.Realizes.fix (2*hist+2)).times vol)).plus (.fix 5))
  have clock : Poly (fun q : PrivateQuery => tally (visitFuel B q.1.1.1.1.length)) := fuel
  have space : Poly (fun q : PrivateQuery => tally (cap B hist q.1.1 q.2)) := bound
  have singleton : Poly (fun q : PrivateQuery => [q.1.2]) :=
    ((show Poly (fun q : PrivateQuery => q.1.2) by fun_prop).pair (Code.Poly.const [])).compose Poly.cons
  have store := (((singleton.pair Easy.snd.poly).pair (Code.Poly.const ([] : List Tally))).compose Easy.some.poly)
  exact (clock.pair ((ctx.pair space).pair store)).compose (evaluate_poly _ h)

private theorem count_names {L : Type} [Fintype L] (order : L ≃ Fin hist) (xs : List (Fin hist)) :
    (∑ l, xs.count (order l)) = xs.length := by
  rw [order.sum_comp (fun j => xs.count j)]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons,List.length_cons,Finset.sum_add_distrib,ih]
    simp

variable {B hist} (order : B.Entry ≃ Fin hist) {f : B.Entry → R} {hf : B.IsSolution f}

private theorem execute_one (visit : Visit VisitContext) (ctx : VisitContext) (job : Job)
    {X : Type} (code : X → Bits.Word) (names : X → List (Fin hist))
    (desc : Descent visit ctx (fun j => size j ≤ (visitRoom B ctx).length) (fun j => (B.recordLimit+1)^j.1.1.length))
    (check : Reads visit ctx [job] code (fun x => (names x).map (tally ∘ Fin.val)))
    (good : size job ≤ (visitRoom B ctx).length) (fuel : (B.recordLimit+1)^job.1.1.length ≤ visitFuel B ctx.1.1.length)
    (count : ∀ x, (names x).length ≤ ctx.1.1.length) (bits tail : Bits.Word) (labels : List Tally) :
    siteEval B hist visit ((ctx,job),bits) = some (tail,labels) ↔
      ∃ x, bits = code x ++ tail ∧ labels = (names x).map (tally ∘ Fin.val) := by
  constructor
  · intro hit
    obtain ⟨n,_,parse⟩ := evaluate_sound visit ctx _ _ [job] bits tail labels hit
    exact (check bits tail labels).mp ⟨n,parse⟩
  · rintro ⟨x,word,rfl⟩
    have correct := (check bits tail _).mpr ⟨x,word,rfl⟩
    refine evaluate_of_descent desc correct (by simpa only [List.mem_singleton,forall_eq] using good)
      _ _ ?_ (visitRoom B ctx).length hist (fun _ ok => ok) ?_ ?_
    · simpa only [List.map_singleton,List.sum_singleton,tally_length] using fuel
    · intro tag mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact (tally_length i.val).le.trans i.isLt.le
    · simp only [tally_length,cap,List.length_map]
      gcongr
      exact count x

set_option maxHeartbeats 1000000 in
/-- Every private input returns exactly the canonical unconsumed suffix and
the local coefficient names, provided the mathematical degree fits the volume. -/
theorem site_execution (visit : Visit VisitContext) (H : ResidentHistory B f hf) (ctx : VisitContext)
    (eqn : ctx.1.1 = H.volume) (big : 1 < H.volume.length) (fits : max 1 (slotDegree S) ≤ gridIndex B H.volume)
    (desc : Descent visit ctx (fun j => size j ≤ (visitRoom B ctx).length) (fun j => (B.recordLimit+1)^j.1.1.length))
    (P : SiteParsers f (source B (gridIndex B H.volume)).network)
    (reads : SiteSpec order visit ctx (H.finalParsers P)
      (inputJob ((gridExecution B f hf H.volume).finalState H.path) H.passes.length))
    (degree : ∀ u h c, (∑ l, ((H.finalParsers P).witnesses u h).exponents c l) ≤ H.volume.length) :
    let Y := (gridExecution B f hf H.volume).finalState H.path
    let Q := H.finalParsers P
    ∀ u h, ∃ names : (Q.witnesses u h).Choice → List (Fin hist),
      (∀ x l, (names x).count (order l) = (Q.witnesses u h).exponents x l) ∧
      ∀ bits tail labels, siteEval B hist visit ((ctx,inputJob Y H.passes.length u h),bits) = some (tail,labels) ↔
        ∃ x, bits = (Q.read u h).encode x ++ tail ∧ labels = (names x).map (tally ∘ Fin.val) := by
  intro Y Q u h
  obtain ⟨names,counts,check⟩ := reads u h
  refine ⟨names,counts,?_⟩
  let j := inputJob Y H.passes.length u h
  apply execute_one visit ctx j _ names desc check
  · change size j ≤ (tally (jobRoom B ctx.1.1.length)).length
    rw [tally_length,eqn]
    exact final_job_size H big fits u h
  · change (B.recordLimit+1)^(tally H.passes.length).length ≤ _
    rw [tally_length,eqn]
    exact history_fuel H big
  · intro x
    rw [eqn,← count_names hist order]
    simpa only [counts] using degree u h x

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
