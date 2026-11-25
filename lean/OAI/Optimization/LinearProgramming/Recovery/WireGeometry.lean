import OAI.Optimization.LinearProgramming.Recovery.BitRestart
import OAI.Optimization.LinearProgramming.Geometry.SubspaceDecision

/-! Geometric labels on the literal finite PCG word stream. Each completed epoch's
simultaneous minor commitment gives one finite hidden instance for exactly its exchanges. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace BitEpoch

open Matrix Submodule OracleSpec PriceGame
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

private theorem observed {ev : List (Event Word)} {q answer : Word} (norestart : restartCount ev=0)
    (mem : (q,answer)∈wordHistory ev) : ∃ b,(q,some b)∈ev ∧ answer=[b] := by
  obtain ⟨⟨w,ans⟩,entry,eq⟩ := List.mem_map.mp (List.mem_reverse.mp mem)
  cases ans with
  | none =>
    have inside : (w,none)∈ev.filter (fun e=>e.2.isNone) := List.mem_filter.mpr ⟨entry,rfl⟩
    have pos:=List.length_pos_of_mem inside
    change 0 < restartCount ev at pos
    omega
  | some b =>
    change (w,[b])=(q,answer) at eq
    cases eq;exact ⟨b,entry,rfl⟩

/-- Convert near geometric inequalities to the exact scalar/wire promise of the
sealed PCG machine; the integer cost vector and unknown active set are shared by all
observed prices, including repeated words and tied minimizers. -/
theorem wire_costs {N R : ℕ} (C : Finset (Fin N→ℝ)) (flag : Bool) (i : Fin N)
    (a : 0 < circuitEnvelope C i) (bounds : ∀ j,0 < circuitEnvelope C j→circuitCost C j∈Set.Icc 0 (R:ℝ))
    (hR : 1 ≤ R) (ev : List (Event Word)) (clean : restartCount ev=0)
    (labels : ∀ (q : Query N) b,(priceQuery q.index q.prices,some b)∈ev→ValidNearLabel C flag q b) :
    ∃ active : Set (Fin N),∃ costs : Fin N→ℕ,i∈active ∧ (∀ j∈active,costs j ≤ R) ∧
      priceConsistent flag active costs (wordHistory ev) := by
  let d:=circuitInstance C flag i a bounds
  let h:=d.rounded
  have side : h.positive=flag := rfl
  have range : d.range=R := circuitInstance_range C flag i a bounds hR
  refine ⟨h.active,fun j=>(h.cost j).val,h.anchor_mem,fun j _=>?_,?_⟩
  · have := (h.cost j).isLt
    change (h.cost j).val < d.range+1 at this
    exact (Nat.le_of_lt_succ this).trans (le_of_eq range)
  · intro j t word mem active minimum
    obtain ⟨b,entry,rfl⟩:=observed clean mem
    let q : Query N := ⟨t,j⟩
    have forced : h.Forced q := by
      refine ⟨active,?_⟩
      intro k hk
      simpa only [q,Hidden.signedPrice,side,adjustedCost] using minimum k hk
    have near := States.Rounding.forced_geometric d (by rfl) q forced
    exact congrArg (fun b : Bool=>[b]) (validNearLabel_on_instance C flag i a bounds q (labels q b entry) near)

/-- A clean physical price history admits one actual bounded finite hidden pricing
instance for the winning orientation. Every recorded bit is used at its own query. -/
theorem circuit_history_consistent {N r s : ℕ}
    (D : Matrix (Fin r) (Fin N) ℚ) (E : Matrix (Fin s) (Fin N) ℚ) (anchor : Fin N)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hDE : D*Eᵀ=0) (dims : r+s=N)
    (F : ℕ) (hF : 1 ≤ F) (flag : Bool)
    (pos : ∀ u v,0 < circuitEnvelope (if flag then minorCircuitFamily D u else minorCircuitFamily E v) anchor)
    (ev : List (Event Word)) (clean : restartCount ev=0) (f : Compression.NonzeroPairMinor D E→ℚ)
    (hf : AdmissibleMinorAssignment D E F f)
    (obs : ∀ (q : Query N) b,(priceQuery q.index q.prices,some b)∈ev→(geometricLabel D E q.prices q.index).eval f=b) :
    ∃ active : Set (Fin N),∃ costs : Fin N→ℕ,anchor∈active ∧ (∀ j∈active,costs j ≤ 2*F) ∧
      priceConsistent flag active costs (wordHistory ev) := by
  let C:=if flag then minorCircuitFamily D (prefixAssignment D E f) else minorCircuitFamily E (dualPrefixAssignment D E f)
  have bound (j : Fin N) (hj : 0 < circuitEnvelope C j) : circuitCost C j∈Set.Icc 0 ((2*F:ℕ):ℝ) := by
    have hb:=prefixAssignment_bounds D E f (Nat.cast_nonneg F) hf.1
    by_cases test : flag=true
    · rw [show C=minorCircuitFamily D (prefixAssignment D E f) from ite_eq_left test] at hj ⊢
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using minorCircuitFamily_costBound D _ (fun k=>(hb k).1) j hj
    · rw [show C=minorCircuitFamily E (dualPrefixAssignment D E f) from ite_eq_right test] at hj ⊢
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using minorCircuitFamily_costBound E _ (fun k=>(hb k).2) j hj
  apply wire_costs C flag anchor (pos _ _) bound (by omega) ev clean
  intro q b mem
  rw [←obs q b mem]
  have hw:=geometricLabel_correct_assignment D E hD hE dims hDE f hf.2 q
  dsimp only [C]
  cases flag
  · exact hw.2
  · exact hw.1


/-- Actual sealed PCG runs recover the rational subspace decision once each uninterrupted
word history is interpreted by the concrete minor/geometry service. The displayed bit time
is for the finite PCG instructions and transfers, in addition to the geometric RAM costs. -/
theorem rational_wire_restarts {S : Type*} {N r s F cap budget : ℕ} {p : BitProgram}
    (D : Matrix (Fin r) (Fin N) ℚ) (E : Matrix (Fin s) (Fin N) ℚ) (anchor : Fin N)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hDE : D*Eᵀ=0) (dims : r+s=N)
    (hF : 1 ≤ F) (serve : S→Word→Reply S) (initial : S)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h q=>[f h q]) (priceInput (2*F) anchor) budget (pricePost (2*F) anchor))
    (capR : ∀ ev t,ServicePath serve initial ev t → restartCount ev ≤ cap)
    (common : ∀ prior start,ServicePath serve initial prior start→∀ ev t,ServicePath serve start ev t → restartCount ev=0→
      ∃ f : Compression.NonzeroPairMinor D E→ℚ,AdmissibleMinorAssignment D E F f ∧
        ∀ (q : Query N) b,(priceQuery q.index q.prices,some b)∈ev→(geometricLabel D E q.prices q.index).eval f=b) :
    ∃ flag : Bool, (flag=true ↔ ∃ x∈span ℚ (Set.range D.row),0 ≤ x ∧ 0 < x anchor) ∧
      ∃ times ev t, Completed p (priceInput (2*F) anchor) serve flag initial times ev t ∧ ServicePath serve initial ev t ∧
        times.length ≤ cap+1 ∧ times.sum ≤ (cap+1)*budget ∧ ev.length ≤ times.sum ∧
        ∀ e∈ev,∃ j : Fin N,∃ prices : Fin N→ℚ,e.1=priceQuery j prices := by
  obtain ⟨flag,side,pos⟩:=exists_winning_circuit_side D E hD hE hDE dims anchor
  refine ⟨flag,side,repeated_sealed_epochs anchor flag serve initial pcg capR ?_⟩
  intro prior start before ev t path clean
  obtain ⟨f,hf,obs⟩:=common prior start before ev t path clean
  exact circuit_history_consistent D E anchor hD hE hDE dims F hF flag pos ev clean f hf obs

end BitEpoch
end Recovery
end LinearProgramming
end Optimization
end OAI
