import OAI.Optimization.LinearProgramming.Compression.ServiceProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceInspectGather
import OAI.Optimization.LinearProgramming.Compression.ServiceContract
import OAI.Optimization.LinearProgramming.Compression.ServiceBranch

/-! Complete service compiler from a closed numerical RAM. The caller sees only a
fixed init and serve ROM. Its input words, sorted generator table, numerical parameter
and heap initialization, tagged answer words, and restart updates are all physically
accounted for. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable OracleSpec OracleSpec.MinorLog GeneratorTable ServiceResources

private theorem assembly {p : Program} {time height : Polynomial ℕ} (solver : NumericSolverSpec p time height)
    {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) (hd : d+e=n)
    (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated (minorProxy D E (manuscriptProxyFuel n)) J)
    (s : State ℚ) (H : ℕ) (persist : Persistent D E J H s.memory) (pub : Index D E)
    (hnative : (heightPolynomial height).eval (totalBits (entries D++entries E)) ≤ H) :
    let q := indexEquiv D E pub
    let r := matrixMinorRequest D E (manuscriptProxyFuel n) J q
    let rom := (ServiceInvoke.numerical p).localBudget
    ∃ t, call (compiledServe p time) ((timePolynomial time rom).eval n) H (resume s (words pub.val)) t ∧
      emits t r ∧ Persistent D E (if r.isNone then insert q J else J) H t.memory := by
  let q := indexEquiv D E pub
  let r := matrixMinorRequest D E (manuscriptProxyFuel n) J q
  let rom := (ServiceInvoke.numerical p).localBudget
  let inp := entries D++entries E
  let B := totalBits inp
  let g := J.card
  let mag := matrixMinorCache D E J q
  let P := fun x => ratBits x ≤ H
  let src := resume s (words pub.val)
  have hg : J.card ≤ paperWidth n := (minorProxy_independent_bound_all D E _ hd J hJ).2
  have magSize := ServiceBudget.magnitudeInput_le D E hd J q hg
  have nB := ServiceBudget.dimension_le_bits D E hd
  obtain ⟨inputSize,innerSize,outputSize⟩ :=
    height_covers height B n (n+totalBits (List.ofFn mag)) nB magSize
  have initialBound : 50*(B+1)^6 ≤ H := inputSize.trans hnative
  have H3 : 3 ≤ H := by have h := Nat.one_le_pow 6 (B+1) (Nat.succ_pos B); omega
  have countSize : ratBits ((J.card+1:ℕ):ℚ) ≤ H := by
    have h := (inspectHeight_bound D E hd hg).2
    exact (nat_bits_le _).trans (by change 3+max (4*(n+1)^2) (J.card+1) ≤ 50*(B+1)^6 at h; omega)
  have counters (i : ℕ) (hi : i ≤ 3+2*onlineMinorBitPolynomial.eval n) : ratBits (i:ℚ) ≤ H := by
    have h := outputSize.trans hnative
    exact (nat_bits_le i).trans (by omega)
  obtain ⟨f,hf,agree⟩ := matrixMinorRequest_common_all D E _ hd J hJ
  have responseSize (v : ℚ) (ok : r=some v) : ratBits v ≤ 3+2*onlineMinorBitPolynomial.eval n := by
    have size := hf.output_bits q
    rw [agree q v ok] at size
    exact size
  obtain ⟨x,k,hk,first,ins,tape⟩ := inspectAndGather_native D E J H s pub hd persist hg initialBound
  obtain ⟨prepared,last,middle,computation,ready,returned,emitted,valueOne⟩ :=
    ServiceDecision.run D E solver J q H x ins tape hg H3 (innerSize.trans hnative)
  have capacity := (ServiceBudget.capacity_bounds time rom n J.card hg).2.2
  obtain ⟨z,finished,rtag,explicit,finalRep⟩ := ServiceBranch.run D E J q r rfl ins ready returned emitted
    valueOne computation.safe_end H3 countSize responseSize counters capacity
  let body := Fragment.seq (Fragment.ofBlock inspectAndGather)
    (.seq (ServiceDecision.decision p time) ServiceBranch.finish)
  have run := (Fragment.Run.ofBlock first).seq (computation.seq finished)
  obtain ⟨t,halt,tag,mem⟩ := ServiceReturn.call_of_run body src z _ H rfl rfl run
  have timeLe : k+(ServicePrepare.work time rom n J.card+1+(2*time.eval n+2)+(postWork n J.card+4))+2 ≤
      (timePolynomial time rom).eval n := by
    apply le_trans _ (time_le time rom n J.card hg)
    unfold totalWork
    omega
  have value (v : ℚ) (h : r=some v) : explicitValue t v := by
    have out := explicit v h
    rw [← mem] at out
    exact out
  have reply : emits t r := by
    cases eq : r with
    | none =>
      change t.output=some 1
      simpa [eq,ServiceDecision.replyTag] using tag.trans (congrArg some rtag)
    | some v =>
      refine ⟨?_,value v eq⟩
      simpa [eq,ServiceDecision.replyTag] using tag.trans (congrArg some rtag)
  refine ⟨t, minorCall_mono halt timeLe le_rfl, reply, ?_⟩
  rw [mem]
  exact finalRep

/-- A single dimension polynomial for the compiled transition's clock and
input-bit polynomial for its rational register height. -/
noncomputable def implementationBudget (p : Program) (time height : Polynomial ℕ) : Polynomial ℕ :=
  timePolynomial time (ServiceInvoke.numerical p).localBudget + heightPolynomial height

/-- The compiler's clock and height witnesses are fixed expressions in the
numerical program and its certified resource polynomials. -/
theorem implements_of_numeric_fixed {p : Program} {time height : Polynomial ℕ}
    (solver : NumericSolverSpec p time height) :
    ImplementsMinorStep (compiledServe p time) ((implementationBudget p time height).eval 1)
      (implementationBudget p time height).natDegree := by
  let tp := timePolynomial time (ServiceInvoke.numerical p).localBudget
  let hp := heightPolynomial height
  let budget := implementationBudget p time height
  intro d e n D E hd J hJ s H hH persist u
  have dom (x : ℕ) : tp.eval x+hp.eval x ≤ polyBound (budget.eval 1) budget.natDegree x := by
    simpa only [budget,implementationBudget,tp,hp,Polynomial.eval_add] using polynomial_eval_le_polyBound budget x
  have size : hp.eval (totalBits (entries D++entries E)) ≤ H :=
    (Nat.le_add_left _ _).trans ((dom _).trans hH)
  obtain ⟨t,call,ev,endstate⟩ := assembly solver D E hd J hJ s H persist u size
  exact ⟨t,minorCall_mono call ((Nat.le_add_right _ _).trans (dom n)) le_rfl,ev,endstate⟩

/-- Existential form of the native transition bound. -/
theorem implements_of_numeric {p : Program} {time height : Polynomial ℕ} (solver : NumericSolverSpec p time height) :
    ∃ c k, ImplementsMinorStep (compiledServe p time) c k :=
  ⟨_,_,implements_of_numeric_fixed solver⟩

/-- From a fully costed closed numerical ROM to the independently fixed public theorem
on the matrices themselves, for every input dimension and every request stream. -/
theorem onlineMinorLogCompression_of_numeric {p : Program} {time height : Polynomial ℕ}
    (solver : NumericSolverSpec p time height) : OnlineMinorLogCompression := by
  obtain ⟨c,k,h⟩ := implements_of_numeric solver
  exact onlineMinorLogCompression_of_implements h

end Compression
end LinearProgramming
end Optimization
end OAI
