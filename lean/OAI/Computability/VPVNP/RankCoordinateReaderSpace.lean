import OAI.Computability.VPVNP.RankCoordinateEvaluator
import OAI.Computability.VPVNP.EvaluatorCallbackSafety

/-! # Preserving the space bound of the evaluator's scalar reader

The native coordinate routine owns the live label, current and next ordinal,
result and private advice ports. Every other evaluator stack is unchanged and
has length bounded by the index word width, scalar degree or scalar word length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Reader

open RAMTape SliceArithmetic Evaluator Evaluator.MatrixCallbacks UniversalCountStack

variable {P : Type} [DecidableEq P] {p e w v : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Algebra (ZMod p) F] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (dim : BurstRAM.Word v) (extra : Stacks P)

/-- Maximum height among the caller's stacks outside the installed routine. -/
def callerPeak (v e w : ℕ) := max v (max w (max e (e*w)))

omit [DecidableEq P] in
private theorem outsideBound (label : ℕ) (i j : Fin dim.val) (acc : F) (q : ReadPort P)
    (outside : ∀ k, mount k ≠ q) :
    ((queryBank (List.replicate label true) (WeightedStep.bank φ w dim i (ordinal dim j) [] acc extra)) q).length
      ≤ callerPeak v e w := by
  rcases q with ⟨⟩ | q
  · exact (outside .label rfl).elim
  · cases q with
    | aux k => exact (outside (.aux k) rfl).elim
    | width => simp [queryBank, WeightedStep.bank, callerPeak]
    | indices k =>
      cases k <;> simp [queryBank, WeightedStep.bank, IndexRegisters.bank, ordinal, callerPeak]
    | arithmetic k =>
      rcases k with k | k
      · simp [queryBank, WeightedStep.bank, MultiplyCall.clean]
      · cases k <;> simp [queryBank, WeightedStep.bank, MultiplyCall.clean, MultiplyCall.external,
          WeightedStep.bits, callerPeak]

/-- The native core's cap and the caller's untouched stacks determine the
physical peak, independently of the time spent computing the coordinate. -/
theorem readsEntryWithin (core : FiniteRoutine (Port P)) (matrix : Matrix (Fin dim.val) (Fin dim.val) F)
    (label time peak : ℕ) (query : ∀ i j : Fin dim.val, ∃ d ≤ time, core.BoundedRun peak d
      (bank (List.replicate label true) (ordinal dim i) (ordinal dim j) [] extra)
      (bank (List.replicate label true) (ordinal dim i) (ordinal dim j) (WeightedStep.bits φ w (matrix i j)) extra)) :
    ReadsEntryWithin φ dim extra (install core) w label time (max peak (callerPeak v e w)) matrix := by
  intro s j
  obtain ⟨d, hd, run⟩ := query s.1 j
  let raw q := queryBank (List.replicate label true) (WeightedStep.bank φ w dim s.1 (ordinal dim j) q s.2 extra)
  let localBank q := bank (List.replicate label true) (ordinal dim s.1) (ordinal dim j) q extra
  have installed (q : List Bool) : installStacks mount (raw []) (localBank q) = raw q := by
    apply installStacks_frame (ports := mount) (base := raw []) (small := localBank q) (target := raw q) mount_injective
    · intro k; cases k <;> rfl
    · intro k outside
      rcases k with ⟨⟩ | k
      · rfl
      · cases k with
        | indices | width | aux => rfl
        | arithmetic k =>
          rcases k with k | k
          · rfl
          · cases k <;> first | rfl | exact (outside .result rfl).elim
  have big : core.BoundedRun (max peak (callerPeak v e w)) d (localBank [])
      (localBank (WeightedStep.bits φ w (matrix s.1 j))) := run.mono_cap (le_max_left ..)
  have mounted := FiniteRoutine.BoundedRun.onPorts (a := core) mount_injective (raw []) big
    (fun k outside ↦ (outsideBound φ dim extra label s.1 j s.2 k outside).trans (le_max_right ..))
  rw [installed, installed] at mounted
  exact ⟨d, hd, mounted⟩

open FiniteSlice RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData

variable [Fintype F] [DecidableEq F] {E : Type*} [Field E] [Algebra F E] [IsAlgClosed E] {t eqs : ℕ}

/-- Packed Cramer execution supplies the full time-and-space matrix callback
on the concrete basis of the reduced algebra. -/
theorem readsEntryWithin_of_suffix (S : QueryData t eqs F) (sys : Fin eqs → MvPolynomial (Fin t) F)
    (h : S.Presents sys) (hd : dim.val = S.dimension)
    (b : Module.Basis (Fin dim.val) F (CoordinateAlgebra F (points sys E)))
    (hb : ∀ i, b i = S.listing sys E (S.basisIndex (Fin.cast hd i)))
    (op : Operation t) (label time peak : ℕ) (core : FiniteRoutine (Port P))
    (query : ∀ current next : Fin dim.val, ∃ d ≤ time, ∃ a : Vector p e,
      φ (value (modulus c) a) = S.stepCoordinate op (Fin.cast hd current) (Fin.cast hd next) ∧
      core.BoundedRun peak d (bank (List.replicate label true) (ordinal dim current) (ordinal dim next) [] extra)
        (bank (List.replicate label true) (ordinal dim current) (ordinal dim next)
          (SliceArithmeticRound.packed w (List.ofFn a)) extra)) :
    ReadsEntryWithin φ dim extra (install core) w label time (max peak (callerPeak v e w))
      ((LinearMap.toMatrixAlgEquiv b) (op.linearAction (coordinateLabel (points sys E)))).transpose := by
  apply readsEntryWithin
  intro current next
  obtain ⟨d, ht, a, hv, run⟩ := query current next
  let M := ((LinearMap.toMatrixAlgEquiv b) (op.linearAction (coordinateLabel (points sys E)))).transpose
  have he : a = scalarEncoding φ (M current next) := (valueEquiv c).injective (φ.injective
    ((hv.trans (S.stepCoordinate_eq_transition sys hd h b hb op current next)).trans (map_scalarEncoding φ _).symm))
  refine ⟨d, ht, ?_⟩
  change core.BoundedRun peak d _ (bank _ _ _ (SliceArithmeticRound.packed w (List.ofFn (scalarEncoding φ (M current next)))) extra)
  rwa [← he]

end RankQuery.Stack.Coordinate.Reader

end VPVNP
end Computability
end OAI
