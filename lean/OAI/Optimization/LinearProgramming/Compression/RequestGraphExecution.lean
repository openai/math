import OAI.Optimization.LinearProgramming.Compression.RequestGraphNative
import OAI.Optimization.LinearProgramming.Compression.RequestScreenCorrespondence
import OAI.Optimization.LinearProgramming.Compression.RequestProbeClock
import OAI.Optimization.LinearProgramming.Compression.RequestDyadicBudget

/-! End-to-end correctness and a polynomial clock for the actual graph request
dialogue. Oracle correctness is required only on physically reachable short rows. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit

def outputWord {n : ℕ} : Option ((Fin n → ℚ) × ℚ) → Word
  | none => Dialogue.outputCode Dialogue.failOutput
  | some (v,c) => Dialogue.outputCode (true,List.ofFn v,c)

private theorem query_mem_prefix {p : ℕ} (o : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    {q : Fin p → ℤ} {k : ℕ} (h : q∈(Lattice.dyadicSearch o a b k).queries) :
    ∃ j<k, q=dyadicQuery a b j (Lattice.dyadicSearch o a b j).numerator := by
  induction k with
  | zero => simp [Lattice.dyadicSearch] at h
  | succ k ih =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨k,by omega,h⟩
    · obtain ⟨j,hj,he⟩ := ih h
      exact ⟨j,by omega,he⟩

private theorem packed_query_rows {n : ℕ} (w : Fin (n+1) → ℚ) (z : Fin (n+1) → ℤ)
    (hz : ‖requestGraph w z‖ ≤ requestCutoff (n+1)) (p : ℕ)
    (o : (Fin ((n+1)+1) → ℤ) → Bool) :
    let q : ℕ := 2^p
    let x : GridArg := (q,List.ofFn z)
    let rs := requestDyadicRows z (Fin.last n) q (gridLower x) (gridWidth x)
    ∀ r ∈ Driver.Probe.queryRows o (dyadicSearchQ rs.1 rs.2 (gridDepth x)),
      ∃ a : Fin ((n+1)+1) → ℤ, r = List.ofFn a ∧
        (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) := by
  intro q x rs r hr
  change r ∈ ((SignQueries.history o (dyadicSearchQ rs.1 rs.2 (gridDepth x))).reverse.map List.ofFn) at hr
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
  rw [List.mem_reverse,dyadicSearchQ_history] at ha
  obtain ⟨j,hj,rfl⟩ := query_mem_prefix o rs.1 rs.2 ha
  have hd : gridDepth x = (2*requestCutoff (n+1)*q).log2+1 := gridDepth_pack q z
  have hl : gridLower x = -(requestCutoff (n+1)*q : ℤ) := gridLower_pack q z
  have hw : (gridWidth x : ℤ) = (2:ℤ)^((2*requestCutoff (n+1)*q).log2+1) := by
    simp [gridWidth,hd]
  have hj' : j < (2*requestCutoff (n+1)*q).log2+1 := by
    rw [← hd]
    exact hj
  refine ⟨_,rfl,?_⟩
  simpa only [rs,hl,hw] using requestDyadic_query_l1 w z (Fin.last n) hz p o j hj'

/-- The initial rounded vector supplies the rational lattice input. The sign service may
depend on history and is constrained only on the allowed homogeneous integer rows. -/
theorem graphRequest_session_from_traced {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (p : ℕ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0)
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (oracle : WordOracle) (initialHistory : Transcript)
    (ho : ∀ hist (a : Fin ((n+1)+1) → ℤ), (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) :
    let input : Input := (2^p,List.ofFn w)
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    let out := outputWord (runMinorRequest w g neg (2^p))
    let len := (inputCode input).length
    ∃ (fresh : Transcript) (rounds : ℕ), WordDialogue.Session inputCode Dialogue.carryCode graphRequestDispatch oracle
      ((Dialogue.dispatchWidthPoly prepareP).eval len) (.inl input) initialHistory out (fresh++initialHistory) rounds ∧
      rounds ≤ (Dialogue.depthPoly prepareP).eval len+1 ∧
      ∀ event∈fresh, ∃ a : Fin ((n+1)+1) → ℤ, event.1=signRowWord a ∧
        (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) := by
  intro input g out len
  let A := nativeGraphRowReducer n w
  let q : ℕ := 2^p
  let L := (Dialogue.dispatchWidthPoly prepareP).eval len
  have hspan := (nativeGraphRowReducer_correct.spec n w).2.2
  have hs : screenRows (Selector.packedTable A) =
      ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) := screenRows_native w A (fun i => by
    rw [← hspan];exact Submodule.subset_span (Set.mem_range_self i))
  have bounds := Dialogue.prepared_bounds prepareP input
  cases hc : requestCandidate w g (Fin.last n) with
  | none =>
    have hm := prepare_pack_miss q w (by simpa [hc] using hs)
    have hstage : graphRequestDispatch (.inl input)=.inl (Dialogue.outputCode Dialogue.failOutput) := by
      change Dialogue.stage (prepare input) = _
      simp [Dialogue.stage,show (prepare input).1=false from hm]
    have hout : out=Dialogue.outputCode Dialogue.failOutput := by simp [out,runMinorRequest,hc,outputWord]
    rw [hout]
    exact ⟨[],1,.done hstage bounds.2.2 (Dialogue.failure_length_le prepareP len),by omega,by simp⟩
  | some index =>
    let z := g index
    let x : GridArg := (q,List.ofFn z)
    have hready : prepare input = (true,x) := prepare_pack_row q w index (by simpa [hc] using hs)
    have hflags := requestCandidate_some hc
    have hres := request_residual_le v z (Fin.last n) hflags.1
      (abs_requestForm_le_of_basis v w z hsign hflags.2)
    let o := affineCommitReply neg
    let O (r : List ℤ) := o (fun i : Fin ((n+1)+1) => readAt (0:ℤ) r i.val)
    have Ocorrect (a : Fin ((n+1)+1) → ℤ) : O (List.ofFn a) = o a := by
      unfold O;congr 1;funext i;exact readAt_ofFn 0 a i
    let rs := requestDyadicRows z (Fin.last n) q (gridLower x) (gridWidth x)
    let qs := Driver.Probe.queryRows o (dyadicSearchQ rs.1 rs.2 (gridDepth x))
    let y := Driver.Probe.coordinate o rs.1 rs.2 (gridDepth x)
    have run : Driver.Probe.Runs O (startProbe x) qs (true,[y]) := startProbe_runs q z O o Ocorrect
    let allowed (r : List ℤ) := ∃ a : Fin ((n+1)+1) → ℤ,
      r=List.ofFn a ∧ (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30)
    have allRows : ∀ r∈qs, allowed r := packed_query_rows w z hflags.2 p o
    have answer (h : Transcript) (r : List ℤ) (hr : allowed r) :
        Driver.nonnegativeAnswer (oracle h (Driver.signPacket r))=O r ∧
          (oracle h (Driver.signPacket r)).length≤2 := by
      obtain ⟨a,rfl,ha⟩ := hr
      rw [Driver.signPacket_pack,Ocorrect]
      exact ho h a ha
    have hstart : graphRequestDispatch (.inl input) = Dialogue.route x (startProbe x) := by
      change Dialogue.stage (prepare input) = _
      rw [hready];rfl
    rw [hready] at bounds
    obtain ⟨fresh,sess,packetTrace⟩ := Dialogue.session_of_probe_runs inputCode prepare x O oracle L
      (x.2.length+1) (gridDepth x) (Dialogue.sourceWordSize x) bounds.2.1 allowed answer
      run allRows (Dialogue.startProbe_bounded x) hstart bounds.2.2 initialHistory
    have hslopes : slopes x.2 = List.ofFn (requestSlope z) := slopes_pack z
    have hgrid : gridOffset x y =
        ((requestGridRun neg z (Fin.last n) q (requestCutoff (n+1))).1 : ℚ)/q :=
      graphOffset_eq_requestGrid v neg hn z hflags.1 q hres
    have hout : out=Dialogue.outputCode (Dialogue.represent x y) := by
      simp only [out,runMinorRequest,hc,Option.map_some,outputWord,Dialogue.represent,hslopes,hgrid]
      rfl
    have hlen : qs.length=gridDepth x := by
      simp only [qs,Driver.Probe.queryRows,List.length_map,List.length_reverse,
        SignQueries.history_length,dyadicSearchQ_cost]
    rw [hout]
    refine ⟨fresh,qs.length+1,sess,by rw [hlen];exact Nat.add_le_add_right bounds.1 1,?_⟩
    intro event he
    have mem : event.1∈fresh.map Prod.fst := List.mem_map.mpr ⟨event,he,rfl⟩
    rw [packetTrace,List.mem_reverse] at mem
    obtain ⟨r,hq,heq⟩ := List.mem_map.mp mem
    obtain ⟨a,hr,ha⟩ := allRows r hq
    exact ⟨a,heq.symm.trans ((congrArg Driver.signPacket hr).trans (Driver.signPacket_pack a)),ha⟩

theorem graphRequest_session_from {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (p : ℕ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0)
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (oracle : WordOracle) (initialHistory : Transcript)
    (ho : ∀ hist (a : Fin ((n+1)+1) → ℤ), (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) :
    let input : Input := (2^p,List.ofFn w)
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    let out := outputWord (runMinorRequest w g neg (2^p))
    let len := (inputCode input).length
    ∃ hist rounds, WordDialogue.Session inputCode Dialogue.carryCode graphRequestDispatch oracle
      ((Dialogue.dispatchWidthPoly prepareP).eval len) (.inl input) initialHistory out hist rounds ∧
      rounds ≤ (Dialogue.depthPoly prepareP).eval len+1 := by
  obtain ⟨fresh,rounds,run,bound,_⟩ := graphRequest_session_from_traced v w p neg hn hsign oracle initialHistory ho
  exact ⟨fresh++initialHistory,rounds,run,bound⟩

theorem graphRequest_session {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (p : ℕ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0)
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (oracle : WordOracle)
    (ho : ∀ hist (a : Fin ((n+1)+1) → ℤ), (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) :
    let input : Input := (2^p,List.ofFn w)
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    let out := outputWord (runMinorRequest w g neg (2^p))
    let len := (inputCode input).length
    ∃ hist rounds, WordDialogue.Session inputCode Dialogue.carryCode graphRequestDispatch oracle
      ((Dialogue.dispatchWidthPoly prepareP).eval len) (.inl input) [] out hist rounds ∧
      rounds ≤ (Dialogue.depthPoly prepareP).eval len+1 :=
  graphRequest_session_from v w p neg hn hsign oracle [] ho

theorem graphRequestMachine_computes {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (p : ℕ) (neg : (Fin (n+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0)
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (oracle : WordOracle)
    (ho : ∀ hist (a : Fin ((n+1)+1) → ℤ), (∑ i, |a i|) ≤ (2:ℤ)^(2*p+8*(n+1)+30) →
      Driver.nonnegativeAnswer (oracle hist (signRowWord a)) = affineCommitReply neg a ∧
        (oracle hist (signRowWord a)).length≤2) :
    let input : Input := (2^p,List.ofFn w)
    let g := fun i => requestDecodeRow (nativeGraphRowReducer n w i)
    graphRequestMachine.ComputesWithin oracle (inputCode input)
      ((Dialogue.runtimePoly prepareP).eval (inputCode input).length)
      (fun _ word => word=outputWord (runMinorRequest w g neg (2^p))) := by
  obtain ⟨hist,rounds,hs,hr⟩ := graphRequest_session v w p neg hn hsign oracle ho
  obtain ⟨t,c,run,ht,halt,_,out⟩ := WordDialogue.machine_computes graphRequestDispatchP oracle hs
  exact ⟨t,c,run,ht.trans (Dialogue.runtime_bound prepareP _ rounds hr),halt,out⟩

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
