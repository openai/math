import OAI.Optimization.LinearProgramming.Compression.RequestGraphExecution
import OAI.Optimization.LinearProgramming.Compression.RequestGraphInputSize
import OAI.Optimization.LinearProgramming.Compression.ProxyHomogeneousFuel

/-! On a real paper request the initial bit tape, every internal word, and the
complete graph-dialogue time are polynomial in the original combinatorial
dimension, independently of the supplied magnitudes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit

noncomputable def paperGraphTime : Polynomial ℕ :=
  (Dialogue.runtimePoly prepareP).comp paperInputPolynomial

/-- Every new sign call made by the graph routine has the correct public field
encoding and fits the manuscript cutoff, in front of the caller's existing transcript. -/
theorem graphRequest_session_paper_for {n : ℕ} (N : ℕ) (hn : n≤paperWidth N)
    (v : Fin (n+1) → ℝ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (oracle : WordOracle) (initial : Transcript) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := roundedFor neg
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    let input : Input := (paperGrid N,List.ofFn w)
    let len := (inputCode input).length
    (∀ hist (a : Fin ((n+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|)≤(2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a))=affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) →
    ∃ (fresh : Transcript) (rounds : ℕ), WordDialogue.Session inputCode Dialogue.carryCode
      graphRequestDispatch oracle ((Dialogue.dispatchWidthPoly prepareP).eval len) (.inl input) initial
      (outputWord (runMinorRequest w g neg (paperGrid N))) (fresh++initial) rounds ∧
      rounds≤(Dialogue.depthPoly prepareP).eval len+1 ∧
      ∀ event∈fresh, ∃ a : Fin ((n+1)+1) → ℤ, event.1=signRowWord a ∧
        (2:ℤ)^p*(∑ i, |a i|)≤(2:ℤ)^fuel := by
  intro p fuel w g input len ho
  have hs := (roundedFor_spec v neg hneg).2
  have hd := Nat.add_le_add_right hn 1
  obtain ⟨fresh,rounds,run,bound,events⟩ := graphRequest_session_from_traced v w p neg hneg hs oracle
    initial (fun hist a ha => ho hist a (manuscript_homogeneous_grid_l1 N _ hd _ ha))
  refine ⟨fresh,rounds,run,bound,?_⟩
  intro event h
  obtain ⟨a,ha,sz⟩ := events event h
  exact ⟨a,ha,manuscript_homogeneous_grid_l1 N _ hd _ sz⟩

theorem graphRequest_session_paper_traced {n : ℕ} (N : ℕ) (hn : n≤paperWidth N)
    (mag : Fin (n+1) → ℚ) (hm : ∀ i, 0 < mag i) (oracle : WordOracle) (initial : Transcript) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := nativeRequestRounded fuel p mag
    let neg := requestMagnitudeNegative fuel p mag
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    let input : Input := (paperGrid N,List.ofFn w)
    let len := (inputCode input).length
    (∀ hist (a : Fin ((n+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|)≤(2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a))=affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) →
    ∃ (fresh : Transcript) (rounds : ℕ), WordDialogue.Session inputCode Dialogue.carryCode
      graphRequestDispatch oracle ((Dialogue.dispatchWidthPoly prepareP).eval len) (.inl input) initial
      (outputWord (runMinorRequest w g neg (paperGrid N))) (fresh++initial) rounds ∧
      rounds≤(Dialogue.depthPoly prepareP).eval len+1 ∧
      ∀ event∈fresh, ∃ a : Fin ((n+1)+1) → ℤ, event.1=signRowWord a ∧
        (2:ℤ)^p*(∑ i, |a i|)≤(2:ℤ)^fuel := by
  intro p fuel w neg g input len ho
  exact graphRequest_session_paper_for N hn (fun i => requestMagnitudeProxy fuel p (mag i)) neg
    (requestMagnitudeNegative_correct fuel p mag hm) oracle initial ho

theorem graphRequestMachine_paper_for {n : ℕ} (N : ℕ) (hn : n≤paperWidth N)
    (v : Fin (n+1) → ℝ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (oracle : WordOracle) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := roundedFor neg
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    (∀ hist (a : Fin ((n+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|) ≤ (2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) →
    graphRequestMachine.ComputesWithin oracle (inputCode (paperGrid N,List.ofFn w))
      (paperGraphTime.eval N) (fun _ word => word=outputWord (runMinorRequest w g neg (paperGrid N))) := by
  intro p fuel w g ho
  obtain ⟨fresh,rounds,session,bound,_⟩ := graphRequest_session_paper_for N hn v neg hneg oracle [] ho
  obtain ⟨time,c,run,ht,halt,_,out⟩ := WordDialogue.machine_computes graphRequestDispatchP oracle session
  have hin := paper_graph_input_length_for N hn v neg hneg
  have htime := Procedure.eval_nat_mono (Dialogue.runtimePoly prepareP) hin
  exact ⟨time,c,run,(ht.trans (Dialogue.runtime_bound prepareP _ rounds bound)).trans
    (by simpa [paperGraphTime] using htime),halt,out⟩

theorem graphRequestMachine_paper {n : ℕ} (N : ℕ) (hn : n≤paperWidth N)
    (mag : Fin (n+1) → ℚ) (hm : ∀ i, 0 < mag i) (oracle : WordOracle) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := nativeRequestRounded fuel p mag
    let neg := requestMagnitudeNegative fuel p mag
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    (∀ hist (a : Fin ((n+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|) ≤ (2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) →
    graphRequestMachine.ComputesWithin oracle (inputCode (paperGrid N,List.ofFn w))
      (paperGraphTime.eval N) (fun _ word => word=outputWord (runMinorRequest w g neg (paperGrid N))) := by
  intro p fuel w neg g ho
  exact graphRequestMachine_paper_for N hn (fun i => requestMagnitudeProxy fuel p (mag i)) neg
    (requestMagnitudeNegative_correct fuel p mag hm) oracle ho

theorem graphRequestMachine_native_reference {n : ℕ} (N : ℕ) (hn : n≤paperWidth N)
    (mag : Fin (n+1) → ℚ) (hm : ∀ i, 0 < mag i) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := nativeRequestRounded fuel p mag
    let neg := requestMagnitudeNegative fuel p mag
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    graphRequestMachine.ComputesWithin (wordSignOracle (referenceOrder neg))
      (inputCode (paperGrid N,List.ofFn w)) (paperGraphTime.eval N)
      (fun _ word => word=outputWord (runMinorRequest w g neg (paperGrid N))) := by
  intro p fuel w neg g
  exact graphRequestMachine_paper N hn mag hm (wordSignOracle (referenceOrder neg))
    (fun hist a _ => reference_reply neg hist a)

/-- The literal machine result for ordered real inputs is the affine row used
in the common-extension and restart theorems. -/
theorem graphRequest_for_indices_using_signs {ι : Type*} [LinearOrder ι] (N : ℕ) (v : ι → ℝ)
    (neg : ∀ J : Finset ι, ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (hneg : ∀ J u a c, neg J u a c=true ↔ requestForm (fun i => v (requestIndices J u i)) a+c<0)
    (J : Finset ι) (u : ι) (hJ : J.card ≤ paperWidth N) (oracle : WordOracle) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let w := roundedFor (neg J u)
    (∀ hist (a : Fin ((J.card+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|) ≤ (2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a))=affineCommitReply (neg J u) a ∧
        (oracle hist (signRowWord a)).length≤2) →
    graphRequestMachine.ComputesWithin oracle (inputCode (paperGrid N,List.ofFn w)) (paperGraphTime.eval N)
      (fun _ word => word=outputWord (requestUsingSigns (paperGrid N) neg J u)) := by
  intro p fuel w ho
  exact graphRequestMachine_paper_for N hJ (fun i => v (requestIndices J u i)) (neg J u) (hneg J u) oracle ho

/-- Use the epoch's ordered generators and appended request index in their
existing order. The emitted option is the ordinary minor-request return value. -/
theorem graphRequest_for_indices {ι : Type*} [LinearOrder ι] (N : ℕ)
    (mag : ι → ℚ) (hm : ∀ i, 0 < mag i) (J : Finset ι) (u : ι) (hJ : J.card≤paperWidth N)
    (oracle : WordOracle) :
    let p := paperRadius N+7
    let fuel := manuscriptProxyFuel N
    let m := fun i => mag (requestIndices J u i)
    let w := nativeRequestRounded fuel p m
    let neg := requestMagnitudeNegative fuel p m
    (∀ hist (a : Fin ((J.card+1)+1) → ℤ), (2:ℤ)^p*(∑ i, |a i|)≤(2:ℤ)^fuel →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a))=affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) →
    graphRequestMachine.ComputesWithin oracle (inputCode (paperGrid N,List.ofFn w)) (paperGraphTime.eval N)
      (fun _ word => word=outputWord (nativeMinorRequest fuel p (paperGrid N) mag J u)) := by
  intro p fuel m w neg h
  exact graphRequestMachine_paper N hJ m (fun i => hm (requestIndices J u i)) oracle h

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
