import OAI.Computability.MultitapeWeakETH.HistoryEvaluator
import OAI.Computability.MultitapeWeakETH.TerminalEnumeration

/-! # Reading a terminal factor from a shared assignment and a padded private word -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory
open NodeArguments WitnessWalk DyadicBudget NetworkKernel TerminalWords TerminalGatherGeometry
open private zeros zeros_iff zeros_poly from OAI.Computability.MultitapeWeakETH.FrameDecoding
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical
noncomputable section

abbrev SiteQuery := (LeafSyntax.Query × SharedData) × Tally
abbrev FactorQuery := SiteQuery × Bits.Word

private def padding (a : Bits.Word × List Tally) := bif zeros a.1 then some a.2 else none

private theorem padding_poly : Poly padding :=
  Poly.choose (Easy.fst.poly.compose zeros_poly) (Easy.snd.compose Easy.some).poly (Code.Poly.const none)

private theorem canonical {X : Type} (read : ChoiceReader X) (bits : Bits.Word) (x : X) :
    ReaderEnumeration.decode read bits = some x ↔ ∃ t, bits = read.encode x ++ t ∧ zeros t = true := by
  rw [ReaderEnumeration.decode_iff]
  constructor
  · rintro ⟨_,e⟩
    refine ⟨_,e,(zeros_iff _).mpr ?_⟩
    simp
  · rintro ⟨t,e,good⟩
    have len := congrArg List.length e
    rw [List.length_append] at len
    refine ⟨by omega,?_⟩
    unfold ReaderEnumeration.padded
    rw [show bits.length - (read.encode x).length = t.length by omega]
    exact e.trans (congrArg _ ((zeros_iff _).mp good))

private theorem padded_result {X : Type} (reader : ChoiceReader X) (run : Bits.Word → Option (Bits.Word × List Tally))
    (names : X → List Tally) (exactRead : ∀ bits tail ls, run bits = some (tail,ls) ↔
      ∃ x, bits = reader.encode x ++ tail ∧ ls = names x) (bits : Bits.Word) (ls : List Tally) :
    (run bits).bind padding = some ls ↔ ∃ x, ReaderEnumeration.decode reader bits = some x ∧ ls = names x := by
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨t,l⟩,got,ok⟩
    obtain ⟨x,e,rfl⟩ := (exactRead ..).mp got
    cases ht : zeros t <;> simp only [padding,ht,Bool.cond_false,Bool.cond_true,reduceCtorEq,Option.some.injEq] at ok
    exact ⟨x,(canonical ..).mpr ⟨t,e,ht⟩,ok.symm⟩
  · rintro ⟨x,found,rfl⟩
    obtain ⟨t,e,ht⟩ := (canonical ..).mp found
    exact ⟨(t,names x),(exactRead ..).mpr ⟨x,e,rfl⟩,by simp only [padding,ht,Bool.cond_true]⟩

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

private def prepareJob (q : SiteQuery) : VisitContext × Job :=
  let src := q.1.1
  let data := q.1.2
  let ordinal := q.2
  let degree := 2^S.degreeExponent 0
  let first := tally (ordinal.length * degree)
  let layer := tally (gridIndex B src.1*(S.steps+1))
  let ids := slots ((first,tally degree),data.1.2.2)
  ((src,data.1.1),((layer,ordinal),gather ((data.1.2.1,data.2),ids)))

private theorem prepare_poly : Poly (prepareJob B) := by
  let reg := (⟨size,send,Dom.base _⟩ : Strip.Regime SiteQuery)
  have pos : Staff.Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : SiteQuery => tally q.2.length)
    simpa only [recover_tally] using (show Poly (fun q : SiteQuery => q.2) by fun_prop)
  have idx : Staff.Realizes reg (fun q => gridIndex B q.1.1.1) :=
    (show Poly (fun q : SiteQuery => q.1.1.1) by fun_prop).compose
      (show Poly (fun v : Tally => tally (gridIndex B v)) from CNFNetwork.SyntaxProgram.index_program _)
  have layer : Poly (fun q : SiteQuery => tally (gridIndex B q.1.1.1*(S.steps+1))) := idx.times (.fix _)
  have first : Poly (fun q : SiteQuery => tally (q.2.length*(2^S.degreeExponent 0))) := pos.times (.fix _)
  let cols := (((first.pair (Code.Poly.const (tally (2^S.degreeExponent 0)))).pair (show Poly (fun q : SiteQuery => q.1.2.1.2.2) by fun_prop))).compose slots_poly
  let data := (show Poly (fun q : SiteQuery => (q.1.2.1.2.1,q.1.2.2)) by fun_prop)
  let ctx := (show Poly (fun q : SiteQuery => (q.1.1,q.1.2.1.1)) by fun_prop)
  exact ctx.pair ((layer.pair Easy.snd.poly).pair ((data.pair cols).compose gather_poly))

theorem prepare_actual {f : B.Entry → R} {hf : B.IsSolution f} (H : ResidentHistory B f hf)
    (q : LeafSyntax.Query) (volume : q.1 = H.volume) :
    let Y := (gridExecution B f hf H.volume).finalState H.path
    ∀ (v : Y.network.Site) (a : Fin (∑ i,TerminalPrefix.width Y i) → Bool),
      prepareJob B ((q,((writes H.log,widths Y,inverse Y),List.ofFn a)),tally ((siteOrder Y).entries.symm v).val) =
        ((q,writes H.log),inputJob Y H.passes.length v (half Y a v)) := by
  intro Y v a
  have layers : H.passes.length = gridIndex B H.volume*(S.steps+1) :=
    VertexLevel.selected_pass_count B f hf _ _ _ H.path
  simp only [prepareJob,inputJob,volume,tally_length,layers]
  change (_,((_,_),gather ((widths Y,List.ofFn a),slots ((tally (firstSlot Y v),tally (2^S.degreeExponent 0)),inverse Y)))) = _
  rw [slots_eq,gather_eq]

def factorEval (hist : ℕ) (visit : Visit VisitContext) (q : FactorQuery) :=
  (siteEval B hist visit (prepareJob B q.1,q.2)).bind padding

theorem factorEval_poly (hist : ℕ) {visit : Visit VisitContext} (h : Poly visit) : Poly (factorEval B hist visit) :=
  bind_poly ([],[]) ((((Easy.fst.poly.compose (prepare_poly B)).pair Easy.snd.poly).compose (siteEval_poly B hist h)))
    (Easy.snd.poly.compose padding_poly)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
