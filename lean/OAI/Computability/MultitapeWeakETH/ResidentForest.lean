import OAI.Computability.MultitapeWeakETH.HistoryVisitExact
import OAI.Computability.MultitapeWeakETH.HistoryForest

/-! # The private words accepted on a complete chronological branch -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords NetworkKernel PairSimulation LocalHistory
open WitnessWalk DyadicBudget NodeArguments
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open scoped Classical
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) {f : B.Entry → R} {hf : B.IsSolution f}

abbrev ResidentHistory.finalParsers (H : ResidentHistory B f hf)
    (P : SiteParsers f (source B (gridIndex B H.volume)).network) :=
  let s := gridIndex B H.volume
  let X := source B s
  LocalHistory.finalParsers ((gridExecution B f hf H.volume).termChain (B.records f hf s (lanes_fit B s) X) H.path)
    (selectedParsers B f hf s (lanes_fit B s) X H.path) P

set_option maxHeartbeats 1000000 in
theorem resident_forest (visit : Visit VisitContext) (ctx : VisitContext) (H : ResidentHistory B f hf)
    (steps : ∀ i : Fin H.passes.length, LayerStep order visit ctx i.val H.passes[i.val])
    (P : SiteParsers f (source B (gridIndex B H.volume)).network)
    (start : SiteSpec order visit ctx P (inputJob (source B (gridIndex B H.volume)) 0)) :
    SiteSpec order visit ctx (H.finalParsers P) (inputJob ((gridExecution B f hf H.volume).finalState H.path) H.passes.length) := by
  let s := gridIndex B H.volume
  let X := source B s
  have allSteps := layerSteps_of_index order visit ctx (first:=0) H.passes
    (fun i => by simpa only [Nat.zero_add] using steps i)
  have walk := branch_forest order visit ctx (gridExecution B f hf H.volume) _ _ _
    (B.records f hf s (lanes_fit B s) X) H.path (execute_originReaders B f hf s (lanes_fit B s) X) 0 allSteps P start
  change SiteSpec order visit ctx (H.finalParsers P) (inputJob _ (0+H.passes.length)) at walk
  rwa [Nat.zero_add] at walk

set_option maxHeartbeats 1600000 in
/-- One tape visitor realizes the selected site parsers at every sufficiently
large volume and for every retained history of a valid sparse formula. -/
theorem formula_forest {A : Type} [_root_.Field A] (g : B.Entry → A) (hg : B.IsSolution g) :
    ∃ visit : Visit VisitContext, Poly visit ∧ ∃ threshold : ℕ,
      ∀ (H : ResidentHistory B g hg) {n bound : ℕ} (F : RawCNF n), 1 < H.volume.length →
        threshold ≤ gridIndex B H.volume → Valid 3 F → SAT.OccurrenceAtMost bound (ExecCNF.formulaSet F) →
        2*n+8*(n*bound)+1 ≤ H.volume.length →
        let X := source B (gridIndex B H.volume)
        let ctx : VisitContext := ((H.volume,tally n,SparseCountProgram.encodeBody F),writes H.log)
        ∃ P : SiteParsers g X.network, contract X.network P.factors = (SAT.count (ExecCNF.formulaSet F) : A) ∧
          (∀ u h c, (P.read u h).encode c = []) ∧ (∀ u h c l, (P.witnesses u h).exponents c l = 0) ∧
          SiteSpec order visit ctx (H.finalParsers P)
            (inputJob ((gridExecution B g hg H.volume).finalState H.path) H.passes.length) := by
  obtain ⟨children,hc,child⟩ := resident_children B g hg
  obtain ⟨sh,refresh,hs,hr,N,kernels⟩ := history_kernels B order g hg
  let visit := visitor (stepSize B) children sh refresh
  refine ⟨visit,visitor_poly _ hc hs hr,max N (max 1 (slotDegree S)),?_⟩
  intro H n bound F volume large valid sparse small X ctx
  obtain ⟨P,count,empty,zero,read⟩ := CNFNetwork.SwitchFactor.source_parsers B g volume F valid sparse small
  refine ⟨P,count,empty,zero,resident_forest order visit ctx H (fun j =>
    resident_node order H _ children sh refresh _ rfl (child H ((le_max_right ..).trans large)) j
      (kernels H ((le_max_left ..).trans large) j)) P ?_⟩
  intro u h
  refine ⟨fun _ => [],fun c l => (zero u h c l).symm,?_⟩
  apply visitor_leaf_reads
  intro bits
  have got := read u h bits
  rw [recover_tally] at got
  exact got

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
