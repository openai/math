import OAI.Optimization.LinearProgramming.Lattice.BitRoundSemanticDigit
import OAI.Optimization.LinearProgramming.Lattice.BitRoundTrace
import OAI.Optimization.LinearProgramming.Lattice.BitProbeCorrect

/-! End-to-end semantics of the finite repeated-direction controller. Every pending request
retains the bounded independent directions and an actual reachable probe continuation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open OracleSpec

/-- The algebraic meaning of the three computations made on well-formed controller inputs.
This interface is instantiated by the fixed, polynomial-time bit-stack kernels. -/
structure RoundKernelSemantics (f : Kernels) : Prop where
  selector : ∀ {p : ℕ} (M : ℕ) (u : Fin p→ℚ), f.selector (M,List.ofFn u) =
    ((lllShortSelector M u).1,List.ofFn (lllShortSelector M u).2)
  finish : ∀ {p : ℕ} (M k : ℕ) (old : List (Fin p→ℤ)), Driver.finish f (packedEnv M k old) =
    .inl (signRowWord (radixVector ((2:ℤ)^radixWidth p M) old.reverse))
  params : ∀ {p : ℕ} (M k : ℕ) (old : List (Fin p→ℤ)),
    LinearIndependent ℝ (fun i : Fin old.length => WithLp.toLp 2 (realCoordinates (old.get i))) →
    probeParams f (packedEnv M k old) =
      ((p,searchPrecision p M),List.ofFn (fun i => List.ofFn (integralRows (residualTableMatrix old) i)))

/-- A witness for the actual outer and inner continuation encoded at a query. -/
def RequestReachedWith (f : Kernels) (p M : ℕ) (u : Request) : Prop :=
  ∃ (left : ℕ) (old : List (Fin p→ℤ)) (row : Row) (c : Probe.Carry),
    DigitInvariant M left old ∧ u=(signPacket row,(packedEnv M left old,c)) ∧
    Probe.Reaches (Probe.start (probeParams f (packedEnv M left old))) (.inr (row,c))

private theorem stage_active (f : Kernels) (e : Env) (hne : e.1.2≠0) :
    stage f e = receiveProbe f e (Probe.start (probeParams f e)) := by
  rw [stage,ite_eq_right hne]
  exact (congrArg (receiveProbe f e) (start_request (probeParams f e))).symm

private theorem receive_selected {f : Kernels} (sem : RoundKernelSemantics f) {p : ℕ} (M k : ℕ) (old : List (Fin p→ℤ)) (u : Fin p→ℚ) :
    receiveProbe f (packedEnv M (k+1) old) (.inl (true,List.ofFn u)) =
    stage f (packedEnv M k ((lllShortSelector M u).2::old)) := by
  change stage f (((p,M),(k+1)-1),(f.selector (M,List.ofFn u)).2::old.map List.ofFn) = _
  rw [sem.selector]; rfl

private theorem map_probe_words {p : ℕ} {α : Type*} (o : (Fin p→ℤ)→Bool) (t : SignQueries p α) :
    (Probe.queryRows o t).map signPacket = wordQueries o t := by
  simp only [Probe.queryRows,wordQueries,List.map_map]
  rfl

/-- Start at any reachable independent direction basis. Future selected rows are appended
to the chronological past when converting the final result to its signed radix vector. -/
theorem stage_directions_with {f : Kernels} (sem : RoundKernelSemantics f) {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (o : (Fin p→ℤ)→Bool) (hO : ∀ a, o a = true ↔ 0≤formValue a v)
    (reply : Word→Word) (wire : ∀ a, rowOracle reply (List.ofFn a)=o a)
    (fuel : ℕ) (old : List (Fin p→ℤ)) (valid : DigitInvariant M fuel old) :
    let t := directionsQ M (lllShortSelector M) fuel old
    ∃ steps : List Request, Dialogue f reply (stage f (packedEnv M fuel old)) steps
      (signRowWord (radixVector ((2:ℤ)^radixWidth p M) (old.reverse++SignQueries.run o t))) ∧
      steps.map Prod.fst=wordQueries o t ∧ ∀ q∈steps, RequestReachedWith f p M q := by
  induction fuel generalizing old with
  | zero =>
    refine ⟨[],?_,rfl,by simp⟩
    change Dialogue _ _ (finish f (packedEnv M 0 old)) [] (signRowWord (radixVector _ (old.reverse++[])))
    rw [sem.finish,List.append_nil]; exact .done _
  | succ k ih =>
    let e := packedEnv M (k+1) old
    let t := probeRowsQ (residualTableMatrix old) (searchPrecision p M)
    let follow : Option (Fin p→ℚ) → SignQueries p (List (Fin p→ℤ)) := fun result => match result with
      | none => .done []
      | some u => let z := (lllShortSelector M u).2
                  (directionsQ M (lllShortSelector M) k (z::old)).bind (fun xs => .done (z::xs))
    let result := SignQueries.run o t
    let out := signRowWord (radixVector ((2:ℤ)^radixWidth p M) (old.reverse++SignQueries.run o (follow result)))
    have suffix : ∃ tail : List Request,
        Dialogue f reply (receiveProbe f e (.inl (Probe.packedResult result))) tail out ∧
        tail.map Prod.fst=wordQueries o (follow result) ∧ ∀ q∈tail, RequestReachedWith f p M q := by
      cases hr : result with
      | none =>
        refine ⟨[],?_,rfl,by simp⟩
        change Dialogue _ _ (finish f e) [] out
        simp only [out,hr,follow,SignQueries.run,List.append_nil,e,sem.finish]
        exact .done _
      | some u =>
        let z := (lllShortSelector M u).2
        have next := valid.next hp hM v o hO old u hr
        obtain ⟨tail,run,qtrace,he⟩ := ih (z::old) next
        refine ⟨tail,?_,?_,he⟩
        · change Dialogue _ _ (receiveProbe f (packedEnv M (k+1) old) (.inl (true,List.ofFn u))) tail out
          rw [receive_selected sem]
          simpa only [out,hr,follow,SignQueries.run_bind,SignQueries.run,List.reverse_cons,List.append_assoc,
            List.singleton_append,z] using run
        · simpa only [follow,wordQueries_bind,wordQueries_done,List.append_nil,z] using qtrace
    obtain ⟨tail,endRun,endWords,endReached⟩ := suffix
    let origin := Probe.start (probeParams f e)
    have physical : Probe.Runs (rowOracle reply) origin (Probe.queryRows o t) (Probe.packedResult result) := by
      unfold origin e
      rw [sem.params M (k+1) old valid.independent]
      exact Probe.start_correct (rowOracle reply) o wire _ _
    obtain ⟨pre,run,words,reached⟩ := probeDialogue f reply e physical Probe.Reaches.refl endRun
    change ∃ qs, Dialogue f reply (stage f e) qs
      (signRowWord (radixVector _ (old.reverse++SignQueries.run o (t.bind follow)))) ∧
      qs.map Prod.fst=wordQueries o (t.bind follow) ∧ ∀ q∈qs,RequestReachedWith f p M q
    refine ⟨pre++tail,?_,?_,?_⟩
    · rw [stage_active f e (by simp [e,packedEnv]),SignQueries.run_bind]
      exact run
    · rw [List.map_append,words,endWords,wordQueries_bind,map_probe_words]
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨row,c,eq,reach⟩ := reached q hq
        exact ⟨k+1,old,row,c,valid,eq,reach⟩
      · exact endReached q hq

/-- Normal input for one fixed transition function.  The entire physical request list
agrees with the typed sign-rounding algorithm, including the terminating zero probe. -/
theorem rounding_dialogue_with {f : Kernels} (sem : RoundKernelSemantics f) {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (o : (Fin p→ℤ)→Bool) (hO : ∀ a, o a = true ↔ 0≤formValue a v)
    (reply : Word→Word) (wire : ∀ a, rowOracle reply (List.ofFn a)=o a) :
    let t := roundingProgramWith M (lllShortSelector M)
    ∃ steps : List Request, Dialogue f reply (dispatch f (.inl (p,M))) steps
      (signRowWord (SignQueries.run o t)) ∧ steps.map Prod.fst = wordQueries o t ∧
      (∀ q∈steps, RequestReachedWith f p M q) ∧ steps.length ≤ p*(2*p+1+p*searchPrecision p M) := by
  obtain ⟨steps,run,qs,reach⟩ := stage_directions_with sem hp hM v o hO reply wire p [] (DigitInvariant.initial p M)
  refine ⟨steps,?_,?_,reach,?_⟩
  · simpa only [dispatch,packedEnv,List.map_nil,List.reverse_nil,List.nil_append,roundingProgramWith,SignQueries.run_bind,
      SignQueries.run] using run
  · simpa only [roundingProgramWith,wordQueries_bind,wordQueries_done,List.append_nil] using qs
  · have h := congrArg List.length qs
    simp only [List.length_map,wordQueries,List.length_reverse,SignQueries.history_length] at h
    exact h.le.trans (cost_directionsQ M (lllShortSelector M) o p [])

/-- The finite ternary wire supplies exactly the required Boolean sign interpretation. -/
theorem rowOracle_wordSignOracle {p : ℕ} (sign : (Fin p→ℤ)→Ordering) (a : Fin p→ℤ) :
    rowOracle (wordSignOracle sign []) (List.ofFn a)=decide (sign a≠.lt) := by
  simp [rowOracle,signPacket_pack,nonnegativeAnswer_sign]

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
