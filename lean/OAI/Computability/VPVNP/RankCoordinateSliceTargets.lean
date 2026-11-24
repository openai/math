import OAI.Computability.VPVNP.RankCoordinateSliceSelection
import OAI.Computability.VPVNP.RankCoordinateTargetRead

/-! # The powered target in the live numerator bank

The ordinary matrix reader and the target reader have disjoint auxiliary
ports. The latter compares the indexed current monomial with the requested
column, returning the native polynomial-basis encoding of zero or one.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.SliceMinors

open RAMTape BurstRAM UniversalCountStack Cursor
open SliceArithmetic FiniteSlice RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData

variable {F : Type} [Field F] [DecidableEq F] {p e t eqs : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    [DecidableEq (AdjoinRoot (modulus c))]
    {K : Type} [Fintype K] [DecidableEq K] {d w v B S A P : ℕ}

/-- Powered-monomial scan template with the slice arity and its two degree bounds fixed, and
the dynamic arguments initialized to zero. -/
def targetTemplate (data : QueryData t eqs F) : PairCall.Inputs where
  arity := t
  degree b := if b then data.columnDegree else data.pointBound
  ordinal _ := 0
  scale := 0
  mark := 0

/-- Installs the current basis monomial, operation scale and variable mark in the target
template. -/
def targetArgs (data : QueryData t eqs F) (op : Operation t) (i : Fin data.dimension) :=
  TargetRead.setDynamic (targetTemplate data) (data.basisIndex i).val (PairCall.targetScale data op) (PairCall.targetMark op)

/-- Disjoint auxiliary ports for the ordinary matrix reader and the powered-target reader. -/
abbrev Direct (K : Type) := K ⊕ TargetRead.Work

/-- Requires the base reader to be ready on its own ports and the powered reader to hold its
target arguments on the other ports. -/
def directReady (c : Vector p e) (w v : ℕ) (q : PairCall.Inputs) (ready : Stacks K → Prop)
    (s : Stacks (Direct K)) : Prop := ready (s ∘ Sum.inl) ∧ TargetRead.Ready c w v q (s ∘ Sum.inr)

/-- Runs the ordinary scalar entry reader using the left auxiliary bank of the direct reader. -/
def ordinary (read : FiniteRoutine (MacaulayRead.Port K)) : FiniteRoutine (MacaulayRead.Port (Direct K)) :=
  MacaulayRead.onAux Sum.inl read

/-- Runs the powered-monomial entry reader using the right auxiliary bank of the direct reader. -/
def powered : FiniteRoutine (MacaulayRead.Port (Direct K)) := MacaulayRead.onAux Sum.inr TargetRead.reader

omit [Fintype K] [DecidableEq K] [NeZero e] [Fact (Irreducible (modulus c))] [DecidableEq (AdjoinRoot (modulus c))] in
theorem directReady_length {ready : Stacks K → Prop} (q : PairCall.Inputs)
    (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A)
    (hw : w ≤ P) (har : q.arity ≤ P) (ht : max P (e*v) ≤ A)
    {s : Stacks (Direct K)} (hs : directReady c w v q ready s) (k : Direct K) : (s k).length ≤ A := by
  rcases k with k | k
  · exact ha _ hs.1 k
  · exact (TargetRead.ready_bound c q hs.2 hw har k).trans ht

omit [Fintype K] [NeZero e] [Fact (Irreducible (modulus c))] [DecidableEq (AdjoinRoot (modulus c))] in
theorem ordinary_correctSpace {n m : ℕ} (q : PairCall.Inputs) (M : Matrix (Fin n) (Fin m) (Scalar c))
    (read : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : w ≤ P) (har : q.arity ≤ P) (ht : max P (e*v) ≤ S) :
    MacaulayRead.CorrectSpace (ordinary read) M w v B S (directReady c w v q ready) := by
  have h := hc.onAux (ready := directReady c w v q ready) (A := S) Sum.inl Sum.inl_injective
    (fun _ hs => hs.1) (fun a out hs ho => by
      constructor
      · simpa only [show installStacks Sum.inl a out ∘ Sum.inl = out from funext (installStacks_at Sum.inl_injective a out)] using ho
      · have eq : installStacks Sum.inl a out ∘ Sum.inr = a ∘ Sum.inr :=
          funext fun j => installStacks_outside a out fun i he => by cases he
        rw [eq]; exact hs.2) (fun s hs j outside => by
      rcases j with j | j
      · exact (outside j rfl).elim
      · exact (TargetRead.ready_bound c q hs.2 hw har j).trans ht)
  simpa only [ordinary, max_self] using h

omit [DecidableEq (AdjoinRoot (modulus c))] in
/-- The exact field encoding of the current powered target at one column. -/
theorem target_flag (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)
    (op : Operation t) (i : Fin data.dimension) (j : Fin (width data)) :
    (if TargetRead.entryFlag (targetArgs data op i) (data.basisIndex i) j then (1 : Scalar c) else 0) =
      target φ data op i j := by
  let f := φ.toRingEquiv.toRingHom.comp (Scalar.interpretation c)
  apply φ.injective.comp (Scalar.interpret_injective c)
  change f _ = f (encode φ _)
  rw [decode_encode]
  exact TargetRead.map_match c f (targetArgs data op i) data op (data.basisIndex i) j rfl rfl

omit [Fintype K] [DecidableEq (AdjoinRoot (modulus c))] in
theorem powered_correctSpace (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)
    (op : Operation t) (i : Fin data.dimension) {ready : Stacks K → Prop} (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A)
    (hw : PairCall.requiredWidth (targetArgs data op i) ≤ w) (hword : w ≤ P) (har : t ≤ P)
    (hlocal : TargetRead.space w P e v ≤ S) (hA : A ≤ S) :
    MacaulayRead.CorrectSpace (powered (K := K))
      (fun _ j => target φ data op i j : Matrix (Fin (height data)) (Fin (width data)) _)
      w v (TargetRead.clock w P e v (targetArgs data op i)) S (directReady c w v (targetArgs data op i) ready) := by
  let q := targetArgs data op i
  have raw := TargetRead.correctSpace (r := height data) (v := v) c q (data.basisIndex i) rfl hw hword har
  have h := raw.onAux (ready := directReady c w v q ready) (A := A) Sum.inr Sum.inr_injective
    (fun _ hs => hs.2) (fun a out hs ho => by
      constructor
      · have eq : installStacks Sum.inr a out ∘ Sum.inl = a ∘ Sum.inl :=
          funext fun j => installStacks_outside a out fun i he => by cases he
        rw [eq]; exact hs.1
      · exact (show installStacks Sum.inr a out ∘ Sum.inr = out from funext (installStacks_at Sum.inr_injective a out)).symm ▸ ho)
    (fun s hs j outside => by
      rcases j with j | j
      · exact ha _ hs.1 j
      · exact (outside j rfl).elim)
  have matrix_eq : (fun _ j => if TargetRead.entryFlag q (data.basisIndex i) j then (1 : Scalar c) else 0 :
      Matrix (Fin (height data)) (Fin (width data)) _) = fun _ j => target φ data op i j :=
    Matrix.ext fun _ j => target_flag φ data op i j
  rw [← matrix_eq]
  exact h.enlarge le_rfl (max_le hlocal hA)

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

/-- Only the scalar entries of the original relation matrix are an input
contract. The target and both pivot scans execute physical finite code.
The common time and space bounds apply to every choice of basis ordinals. -/
theorem native_reads (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (data : QueryData t eqs F)
    (op : Operation t) (current next : Fin data.dimension)
    (scan : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop}
    (hc : MacaulayRead.CorrectSpace scan (baseMatrix φ data) w v B S ready)
    (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A) (base : Stacks K) (hr : ready base)
    (hrSize : height data+height data+(height data+width data)*height data+width data+8 < 2^d)
    (hcSize : width data+width data+(width data+height data)*width data+height data+8 < 2^d)
    (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hp : PairCall.requiredWidth (targetArgs data op current) ≤ w) (hword : w ≤ P) (har : t ≤ P)
    (hbits : max P (e*v) ≤ A) (hA : A ≤ S) (hlocal : TargetRead.space w P e v ≤ S) :
    let n := height data
    let m := width data
    let ticks := selectedTime K n m d w v e B B (TargetRead.clock w P e v (targetTemplate data)) A S
    let cap := selectedSpace K d w v e A S
    let q := targetArgs data op current
    MacaulayRead.CorrectSpace (SelectedMinor.restrictEntry scan scan) (denominator φ data) w v ticks cap
        (Submatrix.Ready (SelectedMinor.Ready w v n m c base ready)) ∧
      MacaulayRead.CorrectSpace (SelectedMinor.numerator scan (ordinary scan) powered) (numerator φ data op current next)
        w v ticks cap (Replacement.Ready w (combinedOrdinal data.equations data.monomials next)
          (Submatrix.Ready (SelectedMinor.Ready w v n m c base (directReady c w v q ready)))) := by
  let q := targetArgs data op current
  have ho := ordinary_correctSpace (P := P) q (baseMatrix φ data) scan hc hword har (hbits.trans hA)
  have ht := powered_correctSpace φ data op current ha hp hword har hlocal hA
  exact selected_reads φ data op current next scan scan (ordinary scan) powered hc hc ho ht ha ha
    (fun _ h k => directReady_length q ha hword har hbits h k) hrSize hcSize hw hv base hr

end RankQuery.Stack.Coordinate.SliceMinors

end

end VPVNP
end Computability
end OAI
