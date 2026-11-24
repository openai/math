import OAI.Computability.VPVNP.RankCoordinatePairReader

/-! # Native Cramer reader for a finite reduced slice algebra

The varying data are the replacement row and target monomial for a particular
pair of basis ordinals. The two determinant tables and the enclosing reader
are fixed throughout the quantification over both ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.NativeReader

open FiniteSlice RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData
open RAMTape Evaluator Evaluator.MatrixCallbacks SliceArithmetic Dispatch Cramer

variable {F : Type} [Field F] [DecidableEq F] {p e : ℕ} [Fact p.Prime] [NeZero e]
  [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
  {A H K L : Type} [DecidableEq A] [DecidableEq H] [Fintype H] [DecidableEq K] [DecidableEq L]
  {t eqs addr v iw B S V peak prep : ℕ}

/-- The rank of the appended equation and monomial rows, hence the common order of both Cramer
minors. -/
abbrev order (S : QueryData t eqs F) := rankQuery (appendRows S.equations S.monomials)

/-- Data presented by the rank selectors and root initializer for one live
query. Both matrix readers have the same physical ABI as the determinant. -/
structure Staged (data : QueryData t eqs F) (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (op : Operation t)
    (dim : BurstRAM.Word iw) (hdim : dim.val = data.dimension) (label : ℕ)
    (host : PairedHost K L ↪ H) (scratch : H) (advice : Stacks A)
    (prepare : FiniteRoutine (Bus A H)) (den : FiniteRoutine (MacaulayRead.Port K))
    (num : FiniteRoutine (MacaulayRead.Port L)) (addr v B S V peak prep : ℕ) (i j : Fin dim.val) where
  /-- The encoded square matrix whose determinant is the denominator for this coordinate query. -/
  denominator : Matrix (Fin (order data)) (Fin (order data)) (Scalar c)
  /-- The encoded square matrix with the selected row replaced by the operation's target row. -/
  numerator : Matrix (Fin (order data)) (Fin (order data)) (Scalar c)
  denMatrix : denominator.map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
    (greedyRowBasis (appendRows data.equations data.monomials)).submatrix id (coordinateColumns _ (greedyRowBasis_fullRank _))
  numMatrix : numerator.map (φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)) =
    replacedMinor (greedyRowBasis (appendRows data.equations data.monomials)) (coordinateColumns _ (greedyRowBasis_fullRank _))
      (data.stepTarget op (Fin.cast hdim i)) (combinedOrdinal data.equations data.monomials (Fin.cast hdim j))
  /-- Condition on the auxiliary stacks from which the denominator entry routine can run. -/
  denReady : Stacks K → Prop
  /-- Condition on the auxiliary stacks from which the numerator entry routine can run. -/
  numReady : Stacks L → Prop
  denReads : MacaulayRead.CorrectSpace den denominator addr v B S denReady
  numReads : MacaulayRead.CorrectSpace num numerator addr v B S numReady
  denBound : ∀ a, denReady a → ∀ k, (a k).length ≤ V
  numBound : ∀ a, numReady a → ∀ k, (a k).length ≤ V
  /-- Private host stacks after preparation, containing both determinant inputs and the
  arithmetic frame. -/
  work : Stacks H
  scratchEmpty : work scratch = []
  /-- Auxiliary Gram-engine stacks prepared for the denominator matrix. -/
  denAux : Stacks (GramEngine.Aux K)
  /-- Auxiliary Gram-engine stacks prepared for the numerator matrix with its replacement row. -/
  numAux : Stacks (GramEngine.Aux L)
  denInput : GramEngine.Ready addr v (order data) (order data) c denReady denAux
  numInput : GramEngine.Ready addr v (order data) (order data) c numReady numAux
  hostInput : ∀ k, work (host k) = SchurPair.host (SchurPair.entryBank c (order data) addr v denAux)
    (SchurPair.entryBank c (order data) addr v numAux) (frame p e v (digits v c) [] [] []) k
  /-- Number of machine ticks taken to prepare the two determinant inputs for this live query. -/
  ticks : ℕ
  clock : ticks ≤ prep
  run : prepare.BoundedRun peak ticks
    (state (List.replicate label true) (Reader.ordinal dim i) (Reader.ordinal dim j) [] advice (fun _ => []))
    (state (List.replicate label true) (Reader.ordinal dim i) (Reader.ordinal dim j) [] advice work)

/-- The native core returns the next-coordinate scalar for either operation. -/
theorem core_step (data : QueryData t eqs F)
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (dim : BurstRAM.Word iw) (hdim : dim.val = data.dimension)
    (op : Operation t) (label : ℕ) (host : PairedHost K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (advice : Stacks A) (prepare : FiniteRoutine (Bus A H)) (den : FiniteRoutine (MacaulayRead.Port K))
    (num : FiniteRoutine (MacaulayRead.Port L)) {d s : ℕ}
    (hv : Word.workingWidth p ≤ v) (hw₃ : 3 ≤ addr) (hw : (d+1)*widthFactor ≤ addr) (hd : d ≤ addr)
    (hsize : order data+order data+0+order data+8 < 2^d)
    (hn : order data ≤ 2^s) (hs : 2*s+6 ≤ addr) (hws : (2*s+6+1)*widthFactor ≤ addr)
    (hquery : PlainEngine.querySpace (order data) addr v e V S ≤ peak) (hroom : (e+1)*(v+1)+divideClock e v ≤ peak)
    (staged : ∀ i j, Nonempty (Staged data φ op dim hdim label host scratch advice prepare den num addr v B S V peak prep i j)) :
    ∀ i j : Fin dim.val, ∃ u ≤ pairTime H prep (order data) addr v e B peak, ∃ a : Vector p e,
      φ (value (modulus c) a) = data.stepCoordinate op (Fin.cast hdim i) (Fin.cast hdim j) ∧
      (pairCore host scratch prepare den num).BoundedRun (peak+returnClock H peak) u
        (state (List.replicate label true) (Reader.ordinal dim i) (Reader.ordinal dim j) [] advice (fun _ : H => []))
        (state (List.replicate label true) (Reader.ordinal dim i) (Reader.ordinal dim j) (digits v a) advice (fun _ : H => [])) := by
  intro i j
  obtain ⟨st⟩ := staged i j
  obtain ⟨u,hu,run⟩ := pairCore_bounded host scratch disjoint prepare den num st.denominator st.numerator
    st.denReads st.numReads st.denBound st.numBound hv hw₃ hw hd hsize hn hs hws hquery hroom
    (List.replicate label true) (Reader.ordinal dim i) (Reader.ordinal dim j) advice st.work st.scratchEmpty
    st.denAux st.numAux st.denInput st.numInput st.hostInput st.run
  refine ⟨u,hu.trans ?_,minorQuotient c st.numerator st.denominator,?_,run⟩
  · unfold pairTime; have := st.clock; omega
  · exact data.minorQuotient_eq_stepCoordinate c φ op _ _ st.numerator st.denominator st.numMatrix st.denMatrix

variable [Fintype F] {E : Type*} [Field E] [Algebra F E] [IsAlgClosed E]

theorem slice_reader (data : QueryData t eqs F) (sys : Fin eqs → MvPolynomial (Fin t) F) (h : data.Presents sys)
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (dim : BurstRAM.Word iw) (hdim : dim.val = data.dimension)
    (basis : Module.Basis (Fin dim.val) F (CoordinateAlgebra F (points sys E)))
    (hb : ∀ i, basis i = data.listing sys E (data.basisIndex (Fin.cast hdim i)))
    (op : Operation t) (label : ℕ) (host : PairedHost K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (advice : Stacks A) (prepare : FiniteRoutine (Bus A H)) (den : FiniteRoutine (MacaulayRead.Port K))
    (num : FiniteRoutine (MacaulayRead.Port L)) {d s : ℕ}
    (hv : Word.workingWidth p ≤ v) (hw₃ : 3 ≤ addr) (hw : (d+1)*widthFactor ≤ addr) (hd : d ≤ addr)
    (hsize : order data+order data+0+order data+8 < 2^d)
    (hn : order data ≤ 2^s) (hs : 2*s+6 ≤ addr) (hws : (2*s+6+1)*widthFactor ≤ addr)
    (hquery : PlainEngine.querySpace (order data) addr v e V S ≤ peak) (hroom : (e+1)*(v+1)+divideClock e v ≤ peak)
    (staged : ∀ i j, Nonempty (Staged data φ op dim hdim label host scratch advice prepare den num addr v B S V peak prep i j)) :
    ReadsEntryWithin φ dim (Sum.elim advice (fun _ : H => [])) (Reader.install (pairCore host scratch prepare den num))
      v label (pairTime H prep (order data) addr v e B peak)
      (max (peak+returnClock H peak) (Reader.callerPeak iw e v))
      ((LinearMap.toMatrixAlgEquiv basis) (op.linearAction (coordinateLabel (points sys E)))).transpose := by
  apply Reader.readsEntryWithin_of_suffix φ dim _ data sys h hdim basis hb op
  exact core_step data φ dim hdim op label host scratch disjoint advice prepare den num hv hw₃ hw hd hsize hn hs hws hquery hroom staged

omit [Fintype F] in
/-- Entrywise form used directly by the evaluator's two callback contracts. -/
theorem entry_reader (data : QueryData t eqs F)
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (dim : BurstRAM.Word iw) (hdim : dim.val = data.dimension)
    (op : Operation t) (label : ℕ) (host : PairedHost K L ↪ H) (scratch : H) (disjoint : ∀ i, host i ≠ scratch)
    (advice : Stacks A) (prepare : FiniteRoutine (Bus A H)) (den : FiniteRoutine (MacaulayRead.Port K))
    (num : FiniteRoutine (MacaulayRead.Port L)) {d s : ℕ}
    (hv : Word.workingWidth p ≤ v) (hw₃ : 3 ≤ addr) (hw : (d+1)*widthFactor ≤ addr) (hd : d ≤ addr)
    (hsize : order data+order data+0+order data+8 < 2^d)
    (hn : order data ≤ 2^s) (hs : 2*s+6 ≤ addr) (hws : (2*s+6+1)*widthFactor ≤ addr)
    (hquery : PlainEngine.querySpace (order data) addr v e V S ≤ peak) (hroom : (e+1)*(v+1)+divideClock e v ≤ peak)
    (staged : ∀ i j, Nonempty (Staged data φ op dim hdim label host scratch advice prepare den num addr v B S V peak prep i j)) :
    ReadsEntryWithin φ dim (Sum.elim advice (fun _ : H => [])) (Reader.install (pairCore host scratch prepare den num))
      v label (pairTime H prep (order data) addr v e B peak) (max (peak+returnClock H peak) (Reader.callerPeak iw e v))
      (fun i j => data.matrixEntry op (Fin.cast hdim j) (Fin.cast hdim i)) := by
  apply Reader.readsEntryWithin
  intro i j
  obtain ⟨u,hu,a,ha,run⟩ := core_step data φ dim hdim op label host scratch disjoint advice prepare den num hv hw₃ hw hd hsize hn hs hws hquery hroom staged i j
  have hz : φ (value (modulus c) a) = data.matrixEntry op (Fin.cast hdim j) (Fin.cast hdim i) :=
    ha.trans (data.matrixEntry_eq_greedyCoordinate op _ _).symm
  have eq := (valueEquiv c).injective (φ.injective (hz.trans (map_scalarEncoding φ _).symm))
  rw [eq] at run; exact ⟨u,hu,run⟩

end RankQuery.Stack.Coordinate.NativeReader

end VPVNP
end Computability
end OAI
