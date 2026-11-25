import OAI.Computability.MultitapeWeakETH.HistoryVisitBounds
import OAI.Computability.MultitapeWeakETH.ResidentForest

/-! # Preserving all valid private codes under a uniform local size cutoff -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation NetworkKernel
open LocalHistory NodeArguments TraversalRows WitnessWalk DyadicBudget
open private accepts_nil from OAI.Computability.MultitapeWeakETH.HistoryVisitCases
open scoped Classical
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) {f : B.Entry → R} {hf : B.IsSolution f}

def visitRoom (B : S.Templates) (ctx : VisitContext) := tally (jobRoom B ctx.1.1.length)

theorem visitRoom_poly (B : S.Templates) : Poly (visitRoom B) := by
  let reg : Strip.Regime VisitContext := ⟨size,send,Dom.base _⟩
  have n : Staff.Realizes reg (fun q => q.1.1.length) := by
    change Poly (fun q : VisitContext => tally q.1.1.length)
    simpa only [recover_tally] using (show Poly (fun q : VisitContext => q.1.1) by fun_prop)
  let t := (Staff.Realizes.fix (2^(4*stepSize B))).times n
  have s : Staff.Realizes reg (fun q => (2^(4*stepSize B)*q.1.1.length)^4) := by
    convert (t.times t).times (t.times t) using 1
    funext q
    ring
  let packet := ((Staff.Realizes.fix 2).times ((((Staff.Realizes.fix (S.steps+1)).times s).plus s).plus
    (((Staff.Realizes.fix 2).times s).times s))).plus (Staff.Realizes.fix 5)
  exact (((packet.plus (.fix 1)).times (.fix (B.recordLimit+1))).plus (.fix 5))

set_option maxHeartbeats 900000 in
theorem guarded_layer (visit : Visit VisitContext) (H : ResidentHistory B f hf) (ctx : VisitContext)
    (volume : ctx.1.1 = H.volume) (big : 1 < H.volume.length) (fits : max 1 (slotDegree S) ≤ gridIndex B H.volume)
    (j : Fin H.passes.length) (actual : LayerStep order visit ctx j.val H.passes[j.val]) :
    LayerStep order (boundedVisit B.recordLimit (visitRoom B) visit) ctx j.val H.passes[j.val] := by
  intro v b
  obtain ⟨names,counts,step⟩ := actual v b
  refine ⟨names,counts,?_⟩
  intro bits jobs tail labels
  rw [boundedVisit_iff,step,and_iff_left_iff_imp]
  rintro ⟨a,x,rfl,rfl,rfl⟩
  obtain ⟨count,space⟩ := history_child_bounds H big fits j v a
  exact ⟨count,by simpa only [visitRoom,tally_length,volume] using space,by simp⟩

private theorem guarded_leaf {D X : Type} (degree : ℕ) (room : D → Tally) (visit : Visit D) (ctx : D) (j : Job)
    (reader : ChoiceReader X) (base : Reads visit ctx [j] reader.encode (fun _ => []))
    (onlyLeaf : ∀ bits js mid ls, visit ((ctx,j),bits) = some ((js,mid),ls) → js = [] ∧ mid = bits)
    (space : replySize [] ≤ (room ctx).length) :
    Reads (boundedVisit degree room visit) ctx [j] reader.encode (fun _ => []) := by
  intro bits tail ls
  rw [← base,accepts_one,accepts_one]
  constructor
  · rintro ⟨js,mid,a,b,hit,sub,out⟩
    obtain ⟨call,_⟩ := (boundedVisit_iff ..).mp hit
    obtain ⟨rfl,rfl⟩ := onlyLeaf _ _ _ _ call
    exact ⟨[],_,a,b,call,(accepts_nil ..).mpr ((accepts_nil ..).mp sub),out⟩
  · rintro ⟨js,mid,a,b,call,sub,out⟩
    obtain ⟨rfl,rfl⟩ := onlyLeaf _ _ _ _ call
    exact ⟨[],_,a,b,(boundedVisit_iff ..).mpr ⟨call,by exact ⟨Nat.zero_le _,space,le_rfl⟩⟩,
      (accepts_nil ..).mpr ((accepts_nil ..).mp sub),out⟩

private theorem leaf_reply (flag : Bool) (bits : Bits.Word) (js : List Job) (mid : Bits.Word) (ls : List Tally)
    (hit : (bif flag then some bits else none).map (fun t => (([],t),[])) = some ((js,mid),ls)) :
    js = [] ∧ mid = bits := by
  cases flag <;> simp only [Bool.cond_true,Bool.cond_false,Option.map_none,Option.map_some,reduceCtorEq,
    Option.some.injEq,Prod.mk.injEq] at hit
  exact ⟨hit.1.1.symm,hit.1.2.symm⟩

/-- The fixed guarded visitor realizes every branch of the same source parser.
The source parser may be chosen before the chronological branch. -/
theorem guarded_visitor :
    ∃ visit : Visit VisitContext, Poly visit ∧ ∃ N : ℕ,
      (∀ ctx, Descent visit ctx (fun j => size j ≤ (visitRoom B ctx).length)
        (fun j => (B.recordLimit+1)^j.1.1.length)) ∧
      ∀ (H : ResidentHistory B f hf) (q : LeafSyntax.Query), q.1 = H.volume → 1 < H.volume.length →
        N ≤ gridIndex B H.volume →
        let X := source B (gridIndex B H.volume)
        ∀ P : SiteParsers f X.network,
        (∀ u h c l, (P.witnesses u h).exponents c l = 0) →
        (∀ u h bits, ((P.read u h).read bits).map Prod.snd =
          CNFNetwork.SwitchFactor.sourceRead (stepSize B) ((q,tally ((siteOrder X).entries.symm u).val,packed X u h),bits)) →
        SiteSpec order visit (q,writes H.log) (H.finalParsers P)
          (inputJob ((gridExecution B f hf H.volume).finalState H.path) H.passes.length) := by
  obtain ⟨children,hc,child⟩ := resident_children B f hf
  obtain ⟨sh,refresh,hs,hr,N,kernels⟩ := history_kernels B order f hf
  let raw := visitor (stepSize B) children sh refresh
  let guard := boundedVisit B.recordLimit (visitRoom B) raw
  refine ⟨guard,boundedVisit_poly _ (visitRoom_poly B) (visitor_poly _ hc hs hr),max N (max 1 (slotDegree S)),
    fun ctx => bounded_descent _ _ _ _ (visitor_lower _ children sh refresh ctx),?_⟩
  intro H q eqn big large X P zeros correct
  have fits := (le_max_right ..).trans large
  apply resident_forest order guard (q,writes H.log) H
  · intro j
    exact guarded_layer order raw H _ eqn big fits j (resident_node order H _ children sh refresh _ eqn
      (child H fits) j (kernels H ((le_max_left ..).trans large) j))
  · intro u h
    refine ⟨fun _ => [],fun c l => (zeros u h c l).symm,?_⟩
    apply guarded_leaf _ _ raw _ _ (P.read u h)
    · exact visitor_leaf_reads _ _ _ _ _ _ _ _ _ (correct u h)
    · intro bits js mid ls hit
      rw [show raw = visitor (stepSize B) children sh refresh from rfl] at hit
      change visitor _ _ _ _ (((q,writes H.log),(([],_),_)),bits) = _ at hit
      rw [visitor_zero] at hit
      unfold CNFNetwork.SwitchFactor.sourceRead at hit
      exact leaf_reply _ bits js mid ls hit
    · simp [visitRoom,replySize,jobRoom]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
