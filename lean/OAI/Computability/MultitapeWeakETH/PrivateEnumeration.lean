import OAI.Computability.MultitapeWeakETH.PrivateCandidate
import OAI.Computability.MultitapeWeakETH.LocalDegrees

/-! # Exact local coefficient labels from a single fixed sparse-formula program -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory Filter
open NodeArguments WitnessWalk DyadicBudget NetworkKernel TerminalWords TerminalGatherGeometry FactorizedCompression
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open private padded_result prepareJob from OAI.Computability.MultitapeWeakETH.PrivateCandidate
open private source_shape from OAI.Computability.MultitapeWeakETH.NativeScale
open private index_tends from OAI.Computability.MultitapeWeakETH.DescriptorReplay
open scoped Classical
noncomputable section

variable {k A : Type} [_root_.Field k] [_root_.Field A] {S : BlockSchedule k} (B : S.Templates)
  {hist : ℕ} (order : B.Entry ≃ Fin hist) (g : B.Entry → A) (hg : B.IsSolution g)

private theorem limit_le (d : ℕ) (v : Tally) : (searchWidth d v).length ≤ v.length := by
  unfold searchWidth
  rw [ruler_length]
  exact (List.length_filter_le ..).trans_eq (by rw [List.length_map,← recover_tally v,Iter.lined,List.length_ofFn,tally_length])

set_option maxHeartbeats 1600000 in
/-- A single polynomial-time callback handles the private index of every
terminal factor. The source decomposition is shared by all histories. -/
theorem private_enumeration :
    ∃ run : FactorQuery → Option (List Tally), Poly run ∧
      ∀ᶠ N : ℕ in atTop, ∀ volume : Tally, volume.length = N →
        ∀ {n bound : ℕ} (F : RawCNF n), Valid 3 F → SAT.OccurrenceAtMost bound (ExecCNF.formulaSet F) →
          2*n+8*(n*bound)+1 ≤ N →
          let X := source B (gridIndex B volume)
          let E := gridExecution B g hg volume
          let L := (searchWidth (2*(4*stepSize B)) volume).length
          let q : LeafSyntax.Query := (volume,tally n,SparseCountProgram.encodeBody F)
          ∃ P : SiteParsers g X.network, contract X.network P.factors = (SAT.count (ExecCNF.formulaSet F) : A) ∧
            ∀ (path : E.Choices) (log : CallProgram.Stores (gridWidth B volume)) (stored : Recorded B g hg volume path log),
              let H : ResidentHistory B g hg := ⟨volume,path,log,stored⟩
              let Y := E.finalState path
              let Q := H.finalParsers P
              ∀ (u : Y.network.Site) (bits : Fin (∑ i,TerminalPrefix.width Y i) → Bool),
                let a := half Y bits u
                ∃ names : (Q.witnesses u a).Choice → List (Fin hist),
                  (∀ x l, (names x).count (order l) = (Q.witnesses u a).exponents x l) ∧
                  (∀ x, ((Q.read u a).encode x).length ≤ L) ∧
                  (∀ x, (∑ l, (Q.witnesses u a).exponents x l) ≤ L) ∧
                  ∀ word ls, run (((q,((writes log,widths Y,inverse Y),List.ofFn bits)),
                    tally ((siteOrder Y).entries.symm u).val),word) = some ls ↔
                    ∃ x, ReaderEnumeration.decode (Q.read u a) word = some x ∧ ls = (names x).map (tally ∘ Fin.val) := by
  obtain ⟨visit,hv,N₀,desc,allReads⟩ := guarded_visitor (f:=g) (hf:=hg) order
  refine ⟨factorEval B hist visit,factorEval_poly B hist hv,?_⟩
  let b := 4*stepSize B
  have hb : 0 < b := by have := step_pos B; dsimp [b]; omega
  filter_upwards [enumeration_bits B g hg,eventually_ge_atTop 2,
    (index_tends hb).eventually (eventually_ge_atTop (max N₀ (max 1 (slotDegree S))))] with N en big large
  intro volume len n bound F valid sparse small X E L q
  subst N
  obtain ⟨P,count,empty,zero,sourceRead⟩ := CNFNetwork.SwitchFactor.source_parsers B g big F valid sparse small
  refine ⟨P,count,?_⟩
  intro path log stored H Y Q u bits a
  have reader := allReads H q rfl big ((le_max_left ..).trans large) P zero (fun v h w => by
    have got := sourceRead v h w
    rw [recover_tally] at got
    exact got)
  let s := gridIndex B volume
  have all := en X (source_shape B s).1 (source_shape B s).2 path
  have lim : L = ⌊(volume.length:ℝ)^(1-1/(2*b:ℝ))⌋₊ := by
    dsimp only [L]
    conv_lhs => rw [← recover_tally volume,searchWidth_eq _ _ (by dsimp [b] at hb; omega),tally_length]
    dsimp [b]
    push_cast
    rfl
  have degree (v h x) : (∑ l, (Q.witnesses v h).exponents x l) ≤ L :=
    (selected_degree B g hg s (lanes_fit B s) X path P zero v h x).trans (lim ▸ Nat.le_floor all.2.2.1)
  obtain ⟨names,counts,checks⟩ := site_execution order visit H (q,writes log) rfl big
    ((le_max_right ..).trans large) (desc _) P reader (fun v h x => (degree v h x).trans (limit_le ..)) u a
  refine ⟨names,counts,fun x => lim ▸ Nat.le_floor (all.2.2.2 P (fun v h x => congrArg List.length (empty v h x)) u a x),degree u a,?_⟩
  intro word ls
  unfold factorEval
  rw [prepare_actual B H q rfl u bits]
  exact padded_result (Q.read u a) _ _ checks word ls

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
