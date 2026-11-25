import OAI.Optimization.LinearProgramming.OracleSpec.NativeAll
import OAI.Optimization.LinearProgramming.Compression.ServiceState
import OAI.Optimization.LinearProgramming.Compression.ProcessRefinement
import OAI.Optimization.LinearProgramming.Compression.ReplyBits
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! Derive the sealed on-demand contract from one physical request transition. The only
implementation input is the costed trace of an actual finite service program. The
transition uses the persistent scalar representation and the externally supplied word
convention. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OracleSpec OracleSpec.MinorLog RAM

/-- Physical simulation obligation for the serving ROM. The ambient scalar height may
be larger than the algorithm's own workspace bound because old scratch cells persist. -/
def ImplementsMinorStep (serve : Program) (c k : ℕ) : Prop :=
  ∀ {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ), d+e=n →
    ∀ (J : Finset (NonzeroPairMinor D E)), IsDissociated (minorProxy D E (manuscriptProxyFuel n)) J →
    ∀ (s : State ℚ) (height : ℕ), polyBound c k (totalBits (entries D ++ entries E)) ≤ height →
      Persistent D E J height s.memory → ∀ u : Index D E,
      let v := indexEquiv D E u
      let r := matrixMinorRequest D E (manuscriptProxyFuel n) J v
      ∃ t, call serve (polyBound c k n) height (resume s (words u.val)) t ∧
        emits t r ∧ Persistent D E (if r.isNone then insert v J else J) height t.memory

noncomputable def serviceBudget (c k : ℕ) : Polynomial ℕ :=
  Polynomial.C c*(Polynomial.X+1)^k+50*(Polynomial.X+1)^2+4*(Polynomial.X+1)+
    3+2*onlineMinorBitPolynomial

private theorem serviceBudget_bounds {c k C K x : ℕ}
    (h : (serviceBudget c k).eval x ≤ polyBound C K x) :
    let B := polyBound C K x
    polyBound c k x + 2*(x+1) ≤ B ∧ 50*(x+1)^2 ≤ B ∧ 4*(x+1) ≤ B ∧
      3+2*onlineMinorBitPolynomial.eval x ≤ B := by
  have val : (serviceBudget c k).eval x=c*(x+1)^k+50*(x+1)^2+4*(x+1)+
      3+2*onlineMinorBitPolynomial.eval x := by simp [serviceBudget]
  rw [val] at h
  dsimp only
  unfold polyBound
  unfold polyBound at h
  omega

private theorem bigger_extension {ι : Type} {n exp large : ℕ} {l : ι → ℝ}
    {h : List (ι × Option ℚ)} (old : extension n exp l h) (he : exp ≤ large) :
    extension n large l h := by
  obtain ⟨f,agree,size,clip⟩ := old
  exact ⟨f,agree,fun i => (size i).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he),clip⟩

/-- The sealed history guarantee with its five outer witnesses fixed. The same
coefficient and exponent bound the time, scalar height and output bit length. -/
def MinorServiceWith (init serve : Program) (C k Cr : ℕ) : Prop :=
  ∀ d e : ℕ, let n := d+e
  ∀ (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ),
    let input := entries D++entries E
    let clock := polyBound C k n
    let height := polyBound C k (totalBits input)
    ∃ ready : State ℚ, call init clock height (start [d,e,n] input) ready ∧
      ready.output = some 0 ∧ ∀ requests : List (Index D E),
      ∃ replies : List (Index D E × Option ℚ),
        Processes (fun u : Index D E => words u.val) serve clock height clock ready requests replies ∧
        restartCount replies ≤ Cr*n^2*((2*n).log2+1) ∧
        ∀ j ≤ replies.length, extension n clock (logarithm D E) (replies.take j)

/-- Expose the initializer, serving program and their common dimension polynomial.
A larger common budget can be chosen in advance for a second scalar domain. -/
theorem minorServiceWith_of_implements {serve : Program} {c k C K : ℕ}
    (machine : ImplementsMinorStep serve c k)
    (bound : ∀ x, (serviceBudget c k).eval x ≤ polyBound C K x) :
    MinorServiceWith minorServiceInitProgram serve C K 15 := by
  intro d e n D E input clock H
  let _ := requestWordOrder D E
  let eqv := indexEquiv D E
  let fuel := manuscriptProxyFuel n
  let l := minorProxy D E fuel
  let proxy := fun u : Index D E => l (eqv u)
  let req := nativePolicy D E
  let rep := fun (J : Finset (Index D E)) (s : State ℚ) => Persistent D E (J.map eqv.toEmbedding) H s.memory
  obtain ⟨time,initClock,_,outBits⟩ := serviceBudget_bounds (bound n)
  obtain ⟨inputBound,_,initBits,_⟩ := serviceBudget_bounds (bound (totalBits input))
  have ctime : polyBound c k n+2*(n+1) ≤ clock := time
  have hbase : polyBound c k (totalBits input) ≤ H := (Nat.le_add_right _ _).trans inputBound
  obtain ⟨ready,init,tag,initial⟩ := minorServiceInit_persistent (n := n) rfl D E
  refine ⟨ready,minorCall_mono init initClock initBits,tag,?_⟩
  have initRep : rep ∅ ready := by simpa [rep] using initial.weaken initBits
  have initDiss : IsDissociated proxy ∅ := by
    intro A hA B hB hne
    exact (hne ((Finset.subset_empty.mp hA).trans (Finset.subset_empty.mp hB).symm)).elim
  have htest : RestartTest proxy req := (matrixMinorRequest_restartTest D E fuel).pullback eqv
  have wbound (u : Index D E) : (words u.val).length ≤ 2*(n+1) := by
    rcases u with ⟨raw, _⟩
    cases raw with
    | inl z => rw [words, squareWords_length]; have hz := z.order.isLt; omega
    | inr z => rw [words, squareWords_length]; have hz := z.order.isLt; omega
  have hbits (J : Finset (Index D E)) (hJ : IsDissociated proxy J) (u : Index D E) (q : ℚ)
      (hq : req J u=some q) : ratBits q ≤ clock := by
    have internal := (isDissociated_map_iff l eqv.toEmbedding J).mpr hJ
    obtain ⟨f,hf,agree⟩ := matrixMinorRequest_common_all D E fuel rfl _ internal
    have fq := agree (eqv u) q hq
    rw [← fq]
    exact (hf.output_bits (eqv u)).trans outBits
  have step (J : Finset (Index D E)) (s : State ℚ) (u : Index D E)
      (hJ : IsDissociated proxy J) (hr : rep J s) :
      ∃ t : State ℚ, call serve (clock-(words u.val).length) H (resume s (words u.val)) t ∧
        emits t (req J u) ∧ rep (if (req J u).isNone then insert u J else J) t := by
    have internal := (isDissociated_map_iff l eqv.toEmbedding J).mpr hJ
    obtain ⟨t,run,reply,persist⟩ := machine D E rfl _ internal s H hbase hr u
    refine ⟨t,minorCall_mono run (by have hw := wbound u; omega) le_rfl,reply,?_⟩
    change Persistent D E ((if (req J u).isNone then insert u J else J).map eqv.toEmbedding) H t.memory
    change Persistent D E (if (req J u).isNone then insert (eqv u) (J.map eqv.toEmbedding) else J.map eqv.toEmbedding)
      H t.memory at persist
    split <;> rename_i h <;> simpa [h] using persist
  intro requests
  have run := serviceEventsFrom_processes (fun u : Index D E => words u.val) serve clock H clock
    proxy req htest rep (fun u => (wbound u).trans (by omega)) hbits step
    requests RequestTrace.start ready initDiss initRep
  obtain ⟨_,_,count,_,extensions⟩ := nativeHistory_correct_all D E rfl requests
  refine ⟨nativeHistory D E requests,run,count,?_⟩
  intro j _
  exact bigger_extension (extensions j) (by omega)

/-- One uniform fixed costed transition suffices. This theorem fixes both programs before
the dimensions, charges the public request read, handles zero columns, and works for
every history length without putting that length into the time or bit bound. -/
theorem onlineMinorLogCompression_of_implements {serve : Program} {c k : ℕ}
    (machine : ImplementsMinorStep serve c k) : OnlineMinorLogCompression := by
  let P := serviceBudget c k
  exact ⟨minorServiceInitProgram,serve,P.eval 1,P.natDegree,15,
    minorServiceWith_of_implements machine (polynomial_eval_le_polyBound P)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
