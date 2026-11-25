import OAI.Optimization.LinearProgramming.Geometry.WireEpoch
import OAI.Optimization.LinearProgramming.Recovery.WireGeometry

/-! Sealed bit-level price recovery connected to the persistent minor-service program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract OracleSpec OracleSpec.MinorLog Matrix Submodule Recovery Recovery.BitEpoch
open scoped Matrix
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- The truth value established by the marked-coordinate theorem. It appears in the
logical postcondition of a run and is independent of the price history. -/
noncomputable def markedSign (D : Matrix (Fin r) (Fin n) ℚ) (anchor : Fin n) : Bool := by
  classical
  exact decide (∃ x∈span ℚ (Set.range D.row),0≤x ∧ 0<x anchor)

@[simp] theorem markedSign_eq_true (D : Matrix (Fin r) (Fin n) ℚ) (anchor : Fin n) :
    markedSign D anchor=true ↔ ∃ x∈span ℚ (Set.range D.row),0≤x ∧ 0<x anchor := by
  classical
  simp [markedSign]

/-- The clean-epoch hypothesis required by a physical bit-PCG execution. It extracts a
single finite cost vector for every word in that epoch, after the genuine prior history. -/
theorem serveWord_clean_of_sign (S : Service D E) (anchor : Fin n) (hD : LinearIndependent ℚ D.row)
    (hE : LinearIndependent ℚ E.row) (hDE : D*Eᵀ=0) (dim : r+s=n) (flag : Bool)
    (meaning : flag=true ↔ ∃ x∈span ℚ (Set.range D.row),0≤x ∧ 0<x anchor)
    (prior : List (Recovery.Event Word)) (start : Contract.History ℚ) (before : Recovery.ServicePath S.serveWord [] prior start)
    (ev : List (Recovery.Event Word)) (last : Contract.History ℚ) (path : Recovery.ServicePath S.serveWord start ev last)
    (clean : Recovery.restartCount ev=0) :
    ∃ active : Set (Fin n), ∃ costs : Fin n → ℕ, anchor∈active ∧ (∀j∈active,costs j≤2*(2^S.outputBits)) ∧
      priceConsistent flag active costs (wordHistory ev) := by
  obtain ⟨sign,exactSign,pos⟩ := exists_winning_circuit_side D E hD hE hDE dim anchor
  have eq : sign=flag := Bool.eq_iff_iff.mpr (exactSign.trans meaning.symm)
  subst sign
  obtain ⟨f,hf,obs⟩ := S.serveWord_common prior start before ev last path clean
  exact circuit_history_consistent D E anchor hD hE hDE dim (2^S.outputBits) Nat.one_le_two_pow flag pos ev clean f hf obs

/-- Specialization to the canonical rational marked-subspace sign, with precisely the
reachable prior and clean suffix expected by `BitEpoch.sealed_epoch`. -/
theorem serveWord_clean_priceConsistent (S : Service D E) (anchor : Fin n) (hD : LinearIndependent ℚ D.row)
    (hE : LinearIndependent ℚ E.row) (hDE : D*Eᵀ=0) (dim : r+s=n)
    (prior : List (Recovery.Event Word)) (start : Contract.History ℚ) (before : Recovery.ServicePath S.serveWord [] prior start)
    (ev : List (Recovery.Event Word)) (last : Contract.History ℚ) (endRun : Recovery.ServicePath S.serveWord start ev last)
    (clean : Recovery.restartCount ev=0) :
    ∃ active : Set (Fin n), ∃ costs : Fin n → ℕ, anchor∈active ∧ (∀j∈active,costs j≤2*(2^S.outputBits)) ∧
      priceConsistent (markedSign D anchor) active costs (wordHistory ev) :=
  S.serveWord_clean_of_sign anchor hD hE hDE dim (markedSign D anchor) (markedSign_eq_true D anchor) prior start before ev last endRun clean

/-- The bit PCG's exact Boolean output decides the rational coordinate, with an actual
persistent service transcript and polynomially many calls to both interfaces. -/
theorem serveWord_recovery (S : Service D E) (anchor : Fin n) (hD : LinearIndependent ℚ D.row)
    (hE : LinearIndependent ℚ E.row) (hDE : D*Eᵀ=0) (dim : r+s=n) (p : BitProgram) (budget : ℕ)
    (pcg : ∀ f : Transcript→Word→Bool, p.ComputesWithin (fun h w => [f h w])
      (priceInput (2*(2^S.outputBits)) anchor) budget (pricePost (2*(2^S.outputBits)) anchor)) :
    ∃ flag : Bool, (flag=true ↔ ∃ x∈span ℚ (Set.range D.row),0≤x ∧ 0<x anchor) ∧
    ∃ times ev last, Completed p (priceInput (2*(2^S.outputBits)) anchor) S.serveWord flag [] times ev last ∧
      Recovery.ServicePath S.serveWord [] ev last ∧ times.length≤S.restartBudget+1 ∧
      times.sum≤(S.restartBudget+1)*budget ∧ ev.length≤times.sum ∧
      (∀ e∈ev,∃ j : Fin n,∃ prices : Fin n→ℚ,e.1=priceQuery j prices) ∧
      ∃ es : List (Index D E × Option ℚ), last=wireHistory es ∧ Follows S.oracle es ∧
        MinorLog.restartCount es=Recovery.restartCount ev ∧ es.length≤ev.length*(r*n) := by
  obtain ⟨flag,meaning,times,ev,last,complete,path,epochs,steps,count,valid⟩ :=
    rational_wire_restarts D E anchor hD hE hDE dim (Nat.one_le_two_pow) S.serveWord [] pcg
      S.serveWord_restartCap S.serveWord_common
  exact ⟨flag,meaning,times,ev,last,complete,path,epochs,steps,count,valid,S.serveWord_traffic ev last path⟩

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
