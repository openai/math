import OAI.Optimization.LinearProgramming.Compression.InnerNativeRound
import OAI.Optimization.LinearProgramming.Compression.InnerValueSizes
import OAI.Optimization.LinearProgramming.Compression.InnerSession
import OAI.Optimization.LinearProgramming.Compression.RequestGraphPaper
import OAI.Optimization.LinearProgramming.Compression.ServiceNumericSpec

/-! Exact numerical and observable-query semantics of the persistent binary controller.
The field oracle is constrained only on well-formed signed rows inside the global budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit SignType ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

private theorem good_append {N p : ℕ} {hs ht : Transcript} (h : goodHistory N p hs) (t : goodHistory N p ht) :
    goodHistory N p (hs++ht) := fun e he => (List.mem_append.mp he).elim (h e) (t e)

private theorem good_epoch {N g : ℕ} {hs : Transcript} (h : goodHistory N (g+1) hs) :
    goodHistory N ((g+1)+1) (historyWith [] epochWire hs) := by
  intro e he
  simp only [historyWith,List.append_nil] at he
  obtain ⟨e',hm,rfl⟩ := List.mem_map.mp he
  obtain ⟨a,ha,hcap⟩ := h e' hm
  refine ⟨padEpochQuery a,?_,?_⟩
  · change epochWire e'.1 = signRowWord (padEpochQuery a)
    exact (congrArg epochWire ha).trans (epochWire_typed a)
  · simpa only [permitted,padEpochQuery_sum_abs] using hcap

/-- Recover the precise affine answer from the typed graph output. -/
def graphValue {g : ℕ} : Option ((Fin g → ℚ) × ℚ) → Graph.Out
  | none => RequestTable.Dialogue.failOutput
  | some (a,c) => (true,List.ofFn a,c)

private theorem graphValue_word {g : ℕ} (r : Option ((Fin g → ℚ) × ℚ)) :
    RequestTable.Dialogue.outputCode (graphValue r) = RequestTable.outputWord r := by
  rcases r with _|⟨a,c⟩ <;> rfl

noncomputable def epochFrame (N g : ℕ) := Driver.frameBound.eval ((g+1)+(epochRadius N g).size+12)
noncomputable def requestFrame (g : ℕ) := Driver.frameBound.eval ((g+2)+(requestRadius g).size+12)
noncomputable def graphFrame (N : ℕ) := (RequestTable.Dialogue.dispatchWidthPoly RequestTable.prepareP).eval
  (RequestTable.paperInputPolynomial.eval N)

def roundCount (p M : ℕ) := p*(2*p+1+p*searchPrecision p M)+1
noncomputable def graphCount (N : ℕ) := (RequestTable.Dialogue.depthPoly RequestTable.prepareP).eval
  (RequestTable.paperInputPolynomial.eval N)+1

private theorem enlarge {I C : Type} {ei : I → Word} {ec : C → Word} {f : I ⊕ (Word × C) → WireAction C}
    {o L L' s h w h' k} (hr : WordDialogue.Session ei ec f o L s h w h' k) (hL : L≤L') :
    WordDialogue.Session ei ec f o L' s h w h' k := by
  induction hr with
  | done step st out => exact .done step (st.trans hL) (out.trans hL)
  | query step st send recv tail ih => exact .query step (st.trans hL) (send.trans hL) (recv.trans hL) ih

/-- The three measured executions produce exactly `numericalValue`. Every packet in the
physical transcript is a well-formed row for the one cache with its scalar-exponent cutoff. -/
theorem native_session_for {g : ℕ} (N : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ)
    (hmember : member=true → rank<g) (v : Fin (g+1) → ℝ) (neg : (Fin (g+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (o : WordOracle) (ho : matchesCoordinates N v o) :
    let x : Input := ((N,g),member,rank)
    let gamma := List.ofFn (sharedEpochCommit N g neg)
    let value := sharedMinorStep N g (position g member rank) neg
    let B := sessionSize x gamma (epochFrame N g) (requestFrame g) (graphFrame N) value
    ∃ h cnt, WordDialogue.Session inputEncoding carryCode dispatch o B (.inl x) [] (outputWord value) h cnt ∧
      cnt≤roundCount (g+1) (epochRadius N g)+roundCount (g+2) (requestRadius g)+graphCount N+1 ∧
      goodHistory N ((g+1)+1) h ∧ (Projector.rowCode gamma).length≤normalizedBound.eval (epochFrame N g) ∧
      (outputWord value).length≤returnBound.eval (max (2*(Projector.rowCode gamma).length+1+graphFrame N)
        ((inputCode x).length+(Projector.rowCode gamma).length+10)) := by
  intro x gamma value B
  let front := fun i : Fin g => v i.castSucc
  let epochNeg := fun (a : Fin g → ℤ) (c : ℤ) => neg (Fin.snoc a 0) c
  let zE := roundZFor (epochRadius N g) epochNeg
  let zR := roundZFor (requestRadius g) neg
  let w := RequestTable.roundedFor neg
  let row := runMinorRequest w (fun i => requestDecodeRow (nativeGraphRowReducer g w i)) neg (paperGrid N)
  let gout := graphValue row
  have posE : 0<epochRadius N g := Nat.zero_lt_succ _
  have posR : 0<requestRadius g := by unfold requestRadius; positivity
  let eo := oracleWith [] epochWire o
  obtain ⟨he,ke,es,ec,eg⟩ := round_session_for N (epochRadius N g) posE front epochNeg
    (epochNegative_correct v neg hn) (manuscript_commit_fuel N g hg) eo (by
      intro h a ha
      change o (historyWith [] epochWire h) (epochWire (signRowWord a)) = _
      rw [epochWire_typed,ho _ _ (by simpa only [permitted,padEpochQuery_sum_abs] using ha),coordinateSign_pad])
  let eh := historyWith [] epochWire he
  let ro := oracleWith eh id o
  obtain ⟨hr,kr,rs,rc,rg⟩ := round_session_for N (requestRadius g) posR v neg hn (manuscript_request_fuel N g hg) ro
    (fun h a ha => ho (historyWith eh id h) a ha)
  let go := oracleWith (hr++eh) id o
  have gwire (h) (a : Fin ((g+1)+1)→ℤ) (ha : permitted N a) :
      Driver.nonnegativeAnswer (go h (signRowWord a))=affineCommitReply neg a ∧ (go h (signRowWord a)).length≤2 := by
    have hx : go h (signRowWord a) = signReply (orderOfSign (coordinateSign v a)) := ho _ a ha
    have reply (s : SignType) : Driver.nonnegativeAnswer (signReply (orderOfSign s)) = decide (0 ≤ s) ∧
        (signReply (orderOfSign s)).length ≤ 2 := by
      cases s <;> decide
    rw [hx]
    exact ⟨(reply (coordinateSign v a)).1.trans (congrFun (coordinateSign_test v neg hn) a),
      (reply (coordinateSign v a)).2⟩
  obtain ⟨hs,ks,gs,gc,gg⟩ := RequestTable.graphRequest_session_paper_for N hg v neg hn go [] gwire
  let glen := (RequestTable.inputCode (paperGrid N,List.ofFn w)).length
  have hlength : glen ≤ RequestTable.paperInputPolynomial.eval N := RequestTable.paper_graph_input_length_for N hg v neg hn
  have gframe := Procedure.eval_nat_mono (RequestTable.Dialogue.dispatchWidthPoly RequestTable.prepareP) hlength
  have gcount : (RequestTable.Dialogue.depthPoly RequestTable.prepareP).eval glen ≤
      (RequestTable.Dialogue.depthPoly RequestTable.prepareP).eval (RequestTable.paperInputPolynomial.eval N) :=
    Procedure.eval_nat_mono _ hlength
  have hsGraph : WordDialogue.Session RequestTable.inputCode RequestTable.Dialogue.carryCode RequestTable.graphRequestDispatch
      go (graphFrame N) (.inl (paperGrid N,normalizeRow (List.ofFn zR))) [] (RequestTable.Dialogue.outputCode gout) hs ks := by
    have normalized : normalizeCommit zR = w := rfl
    have output : RequestTable.Dialogue.outputCode gout = RequestTable.outputWord row := graphValue_word row
    rw [normalizeRow_pack,normalized,output]
    dsimp only [graphFrame,row,w]
    have enlarged := enlarge gs gframe
    simp only [List.append_nil] at enlarged
    exact enlarged
  have hGamma : normalizeRow (List.ofFn zE)=gamma := by rw [normalizeRow_pack]; exact congrArg List.ofFn (sharedGamma_for N neg).symm
  have hval : combinedAnswer x gamma gout=value := by
    change combinedAnswer ((N,g),member,rank) gamma (graphValue row)=sharedMinorStep N g (position g member rank) neg
    cases member with
    | false =>
      have hp : position g false rank=none := by simp [position]
      rw [hp]
      change affineResult gamma (graphValue row)=row.map _
      rcases hrow : row with _ | ⟨a,c⟩
      · rfl
      · exact affineResult_pack _ _ _
    | true =>
      have hi : rank<g := hmember rfl
      have hp : position g true rank=some ⟨rank,hi⟩ := by simp [position,hi]
      rw [hp]
      exact congrArg some (readAt_ofFn (0:ℚ) (sharedEpochCommit N g neg) (⟨rank,hi⟩:Fin g))
  obtain ⟨final,cnt,ct,session,hhist⟩ := assembleSessions x o (List.ofFn zE) (List.ofFn zR) gout
    (epochFrame N g) (requestFrame g) (graphFrame N) ke kr ks he hr hs es rs hsGraph
  refine ⟨final,cnt,by simpa only [hGamma,hval] using session,?_,?_,?_,?_⟩
  · have graphCalls : ks ≤ graphCount N := gc.trans (Nat.add_le_add_right gcount 1)
    exact ct.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ec rc) graphCalls) 1)
  · rw [hhist]
    split
    · exact good_epoch eg
    · exact good_append gg (good_append rg (good_epoch eg))
  · rw [← hGamma]
    exact normalized_length (sessionOutputLength es)
  · rw [← hval]
    exact combined_length x gamma gout (graphFrame N) (sessionOutputLength hsGraph)

theorem native_session {g : ℕ} (N : ℕ) (hg : g≤paperWidth N) (member : Bool) (rank : ℕ)
    (hmember : member=true → rank<g) (mag : Fin (g+1) → ℚ) (hm : ∀ i,0 < mag i) (o : WordOracle)
    (ho : «matches» N mag o) :
    let x : Input := ((N,g),member,rank)
    let neg := requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) mag
    let gamma := List.ofFn (sharedEpochCommit N g neg)
    let value := numericalValue N (position g member rank) mag
    let B := sessionSize x gamma (epochFrame N g) (requestFrame g) (graphFrame N) value
    ∃ h cnt, WordDialogue.Session inputEncoding carryCode dispatch o B (.inl x) [] (outputWord value) h cnt ∧
      cnt≤roundCount (g+1) (epochRadius N g)+roundCount (g+2) (requestRadius g)+graphCount N+1 ∧
      goodHistory N ((g+1)+1) h ∧ (Projector.rowCode gamma).length≤normalizedBound.eval (epochFrame N g) ∧
      (outputWord value).length≤returnBound.eval (max (2*(Projector.rowCode gamma).length+1+graphFrame N)
        ((inputCode x).length+(Projector.rowCode gamma).length+10)) := by
  let fuel := manuscriptProxyFuel N
  let p := paperRadius N+7
  exact native_session_for N hg member rank hmember (generatorProxy fuel p mag)
    (requestMagnitudeNegative fuel p mag) (requestMagnitudeNegative_correct fuel p mag hm) o
    (matches_coordinates_of_magnitudes mag hm o ho)

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
