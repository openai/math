import OAI.Computability.VPVNP.RankQueryReaderFits

/-! # The native Cramer entries at the common reader-plan budgets

A single advised width accommodates both orientations of the rectangular
matrix, the two monomial decoders and the target shift. The polynomial
space and logarithmic time estimates for the planned minor apply to each
operation and both runtime basis ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.SliceMinors

open RAMTape BurstRAM Cursor ConcreteResources
open SliceArithmetic FiniteSlice RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData

variable {F : Type} [Field F] [DecidableEq F] {p e : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    [DecidableEq (AdjoinRoot (modulus c))] {K : Type} [Fintype K] [DecidableEq K]

/-- Compare prefix-rank scan ports when mounting the planned minor readers. -/
local instance : DecidableEq (PrefixPort K) := inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))
/-- Decide equality of workspace ports for the planned greedy row and column selections. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) := fun a b => PrefixWorkspace.instDecidableEqAux a b
/-- Compare addresses within one pivot-selection bank using the prefix-word register layout. -/
local instance : DecidableEq (Select.Side K) := inferInstanceAs (DecidableEq (PrefixWords.Port (PrefixWorkspace.Aux (PrefixPort K))))
/-- Compare addresses of the two pivot banks and the scalar-reader portion of a planned minor. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Host K J) :=
  inferInstanceAs (DecidableEq (Select.Side K ⊕ (Select.Side K ⊕ J)))
/-- Decide equality of the planned selected-minor workspace ports through the submatrix
reader's representation. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Work K J) := fun a b => Submatrix.instDecidableEqWork a b

variable {t eqs d w v B A S : ℕ}

/-- Passing `canonicalFits` for the reader plan supplies every shape, width
and target bound. The two matrices use the common planned minor budget. -/
theorem native_reads_of_plan (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F)
    (data : QueryData t eqs F) (fit : CanonicalFits data d w v e A S B)
    (op : Operation t) (current next : Fin data.dimension)
    (scan : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop}
    (hc : MacaulayRead.CorrectSpace scan (baseMatrix φ data) w v B S ready)
    (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A)
    (base : Stacks K) (hr : ready base) (hfield : Word.workingWidth p ≤ v) :
    let n := height data
    let m := width data
    let budget := minorBudget K n m d w v e B A S B
    let numReady := directReady c w v (targetArgs data op current) ready
    MacaulayRead.CorrectSpace (SelectedMinor.restrictEntry scan scan) (denominator φ data) w v budget.time budget.space
        (Submatrix.Ready (SelectedMinor.Ready w v n m c base ready)) ∧
      MacaulayRead.CorrectSpace (SelectedMinor.numerator scan (ordinary scan) powered) (numerator φ data op current next)
        w v budget.time budget.space (Replacement.Ready w (combinedOrdinal data.equations data.monomials next)
          (Submatrix.Ready (SelectedMinor.Ready w v n m c base numReady))) := by
  obtain ⟨hp,hclock,hspace⟩ := fit.target op current
  obtain ⟨den,num⟩ := native_reads φ data op current next scan hc ha base hr fit.rowShape fit.columnShape
    fit.gramFit hfield hp fit.wordLive fit.arityLive fit.scalarLive fit.liveSpace hspace
  have time_bound : selectedTime K (height data) (width data) d w v e B B
      (TargetRead.clock w A e v (targetTemplate data)) A S ≤
      (minorBudget K (height data) (width data) d w v e B A S B).time := by
    dsimp only [selectedTime,minorBudget]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_right
    apply max_le_max le_rfl
    exact Nat.add_le_add_right (Nat.add_le_add_left hclock _) _
  exact ⟨den.enlarge time_bound le_rfl, num.enlarge time_bound le_rfl⟩

omit [NeZero e] [Algebra (ZMod p) F] [Fact (Irreducible (modulus c))] [DecidableEq (AdjoinRoot (modulus c))] in
/-- Both auxiliary states at instruction boundaries share the planned
height bound, including the three live target arguments. -/
theorem planned_ready_bounds (data : QueryData t eqs F) (fit : CanonicalFits data d w v e A S B)
    (op : Operation t) (current : Fin data.dimension)
    {ready : Stacks K → Prop} (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A)
    (base : Stacks K) (hr : ready base) (replace : ℕ) :
    let n := height data
    let m := width data
    let limit := SelectedMinor.space K d w v e A S
    let dn := Submatrix.Ready (SelectedMinor.Ready w v n m c base ready)
    let nu := Replacement.Ready w replace (Submatrix.Ready
      (SelectedMinor.Ready w v n m c base (directReady c w v (targetArgs data op current) ready)))
    (∀ bank, dn bank → ∀ k, (bank k).length ≤ limit) ∧ (∀ bank, nu bank → ∀ k, (bank k).length ≤ limit) := by
  have hd := fun s h k => directReady_length (c := c) (ready := ready) (targetArgs data op current) ha
    fit.wordLive fit.arityLive fit.scalarLive (s := s) h k
  exact ⟨SelectedMinor.den_ready_length base hr ha ha fit.rowFit fit.columnFit,
    SelectedMinor.num_ready_length base hr ha hd fit.rowFit fit.columnFit replace⟩

end RankQuery.Stack.Coordinate.SliceMinors

end

end VPVNP
end Computability
end OAI
