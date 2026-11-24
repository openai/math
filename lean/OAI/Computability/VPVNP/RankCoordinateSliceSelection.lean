import OAI.Computability.VPVNP.RankCoordinateSliceFieldEquiv

/-! # Greedy minor readers for a live finite-slice query

The two pivot templates depend only on the base relation matrix. The
numerator has a separate direct reader bank for the currently staged
powered monomial and the replacement row. Both physical readers use the
same clock and stack cap expected by the paired determinant machine.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack

open RAMTape

theorem MacaulayRead.CorrectSpace.enlarge {K : Type} [DecidableEq K] {p e n m w v B B' S S' : ℕ}
    {c : SliceArithmetic.Vector p e} {read : FiniteRoutine (MacaulayRead.Port K)}
    {M : Matrix (Fin n) (Fin m) (Scalar c)} {ready : Stacks K → Prop}
    (h : MacaulayRead.CorrectSpace read M w v B S ready) (hb : B ≤ B') (hs : S ≤ S') :
    MacaulayRead.CorrectSpace read M w v B' S' ready := by
  intro i j s hr
  obtain ⟨u,hu,o,ho,run⟩ := h i j s hr
  exact ⟨u,hu.trans hb,o,ho,run.enlarge hs⟩

namespace Coordinate.SliceMinors

open SliceArithmetic RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData
open FiniteSlice BurstRAM Dispatch Cursor

variable {F : Type} [Field F] [DecidableEq F] {p e t eqs : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    [DecidableEq (AdjoinRoot (modulus c))]
    {K D R : Type} [Fintype K] [DecidableEq K] [DecidableEq D] [DecidableEq R]
    {d w v B Ba Bt S A : ℕ}

/-- Compares the ports of a prefix-rank call using the underlying Gram-scan address type. -/
local instance : DecidableEq (PrefixPort K) := inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))
/-- Decides equality of auxiliary addresses in the greedy prefix scanner. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) := fun a b => PrefixWorkspace.instDecidableEqAux a b
/-- Compares the register and auxiliary addresses of a row or column selector. -/
local instance : DecidableEq (Select.Side K) := inferInstanceAs (DecidableEq (PrefixWords.Port (PrefixWorkspace.Aux (PrefixPort K))))

/-- Distinguishes the two selector banks and the direct entry reader inside a selected minor. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Host K J) :=
  inferInstanceAs (DecidableEq (Select.Side K ⊕ (Select.Side K ⊕ J)))
/-- Compares the selected row word, column word and remaining selected-minor workspace
addresses. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Work K J) := fun a b => Submatrix.instDecidableEqWork a b

/-- Row count of the appended matrix, comprising equation multiples and monomials up to the
point bound. -/
abbrev height (data : QueryData t eqs F) := eqs*size t data.multiplierDegree+size t data.pointBound
/-- Column count of the slice matrix, given by the number of monomials up to its column degree. -/
abbrev width (data : QueryData t eqs F) := size t data.columnDegree

/-- Time bound for a selected entry, covering the slower of the ordinary and powered readers
and the row-replacement overhead. -/
def selectedTime (K : Type) [Fintype K] (n m d w v e B Ba Bt A S : ℕ) :=
  20*w+10 + (max (SelectedMinor.time K n m d w v e B A S Ba) (SelectedMinor.time K n m d w v e B A S Bt)+1)

/-- Peak stack height for a selected entry, including the workspace needed to test the
replacement row. -/
def selectedSpace (K : Type) [Fintype K] (d w v e A S : ℕ) :=
  max (SelectedMinor.space K d w v e A S) (w+(20*w+10))

/-- Physical readers for the exact two matrices in the finite-slice Cramer
quotient. The three direct scalar programs may use different predicates and
banks from the immutable pivot matrix reader. -/
theorem selected_reads (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)
    (op : Operation t) (current next : Fin data.dimension)
    (scan : FiniteRoutine (MacaulayRead.Port K)) (denEntry : FiniteRoutine (MacaulayRead.Port D))
    (numEntry power : FiniteRoutine (MacaulayRead.Port R))
    {pivot : Stacks K → Prop} {denReady : Stacks D → Prop} {numReady : Stacks R → Prop}
    (hs : MacaulayRead.CorrectSpace scan (baseMatrix φ data) w v B S pivot)
    (hd : MacaulayRead.CorrectSpace denEntry (baseMatrix φ data) w v Ba S denReady)
    (hn : MacaulayRead.CorrectSpace numEntry (baseMatrix φ data) w v Ba S numReady)
    (ht : MacaulayRead.CorrectSpace power (fun _ j => target φ data op current j :
      Matrix (Fin (height data)) (Fin (width data)) _) w v Bt S numReady)
    (hsCap : ∀ a, pivot a → ∀ k, (a k).length ≤ A)
    (hdCap : ∀ a, denReady a → ∀ k, (a k).length ≤ A)
    (hnCap : ∀ a, numReady a → ∀ k, (a k).length ≤ A)
    (hrSize : height data+height data+(height data+width data)*height data+width data+8 < 2^d)
    (hcSize : width data+width data+(width data+height data)*width data+height data+8 < 2^d)
    (hw : gramWidth d ≤ w) (hv : Word.workingWidth p ≤ v) (base : Stacks K) (hr : pivot base) :
    let n := height data
    let m := width data
    let ticks := selectedTime K n m d w v e B Ba Bt A S
    let cap := selectedSpace K d w v e A S
    MacaulayRead.CorrectSpace (SelectedMinor.restrictEntry scan denEntry) (denominator φ data) w v ticks cap
        (Submatrix.Ready (SelectedMinor.Ready w v n m c base denReady)) ∧
      MacaulayRead.CorrectSpace (SelectedMinor.numerator scan numEntry power) (numerator φ data op current next) w v ticks cap
        (Replacement.Ready w (combinedOrdinal data.equations data.monomials next)
          (Submatrix.Ready (SelectedMinor.Ready w v n m c base numReady))) := by
  let M := baseMatrix φ data
  have dn := SelectedMinor.restrictEntry_correctSpace M M scan denEntry hs hd hsCap hdCap hrSize hcSize hw hv base hr
  have nu := SelectedMinor.numerator_correctSpace M (target φ data op current) scan numEntry power hs hn ht
    hsCap hnCap hrSize hcSize hw hv base hr (nativeOrdinal φ data next)
  have hdcast := dn.castSquare (interpretedRank φ data) (denominator_cast_apply φ data)
  have hncast := nu.castSquare (interpretedRank φ data) (numerator_cast_apply φ data op current next)
  refine ⟨hdcast.enlarge ?_ (le_max_left ..), hncast⟩
  exact (le_max_left ..).trans ((Nat.le_add_right _ _).trans (Nat.le_add_left ..))

end Coordinate.SliceMinors
end RankQuery.Stack

end

end VPVNP
end Computability
end OAI
