import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPackedCensusRows

namespace OAI
/-! # Exact two-bit census tags of the compiled physical signed cable panel -/
namespace Hierarchy.DescentSharedCableNames
open DescentColonies DescentSIMDLookup DescentSixParty DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
namespace Stage
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Host J V k↪ℕ)
local notation "B" => source A native
local notation "fit" => measured A native S ready
local notation "roster" => neighbors A native names

/-- Projection to the exact signed census digit, including dead padding. -/
theorem census_tags (h : Host J V k) (s : Fin (2*A.cap)) :
    censusTag (signedPanel A native S ready names h s)=
      PackedCensus.tags (Finset.univ.map (signed A native S ready h.1 h.2))
        (Finset.univ.map ((PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2).trans
          (signed A native S ready h.1 h.2))) s := by
  let addr:=signed A native S ready h.1 h.2
  let pick:=PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2
  by_cases occupied : ∃p,addr p=s
  · obtain ⟨p,rfl⟩:=occupied
    have alive : addr p∈Finset.univ.map addr :=Finset.mem_map.mpr ⟨p,Finset.mem_univ _,rfl⟩
    have pay : addr p∈Finset.univ.map (pick.trans addr) ↔ isMarkedOut A h p=true := by
      rw [marked_iff]
      simp only [Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.trans_apply,Function.Embedding.apply_eq_iff_eq,pick]
    rw [census_read]
    change _=if addr p∈Finset.univ.map (pick.trans addr) then 3 else if addr p∈Finset.univ.map addr then 1 else 0
    by_cases marked : isMarkedOut A h p = true
    · simp only [ite_eq_left marked, ite_eq_left (pay.mpr marked)]
    · have unpaid := fun mem => marked (pay.mp mem)
      simp only [ite_eq_right marked, ite_eq_right unpaid, ite_eq_left alive]
  · have no : ∀p,addr p≠s:=not_exists.mp occupied
    have hole : s∉Finset.univ.map addr := by simpa only [Finset.mem_map,Finset.mem_univ,true_and] using occupied
    have unpaid : s∉Finset.univ.map (pick.trans addr) :=by
      rintro hs
      obtain ⟨o,_,eqn⟩:=Finset.mem_map.mp hs
      exact no (pick o) eqn
    rw [signed_empty A native S ready names h s no]
    change 0=if s∈Finset.univ.map (pick.trans addr) then 3 else if s∈Finset.univ.map addr then 1 else 0
    rw [ite_eq_right unpaid,ite_eq_right hole]
end Stage
end
end Hierarchy.DescentSharedCableNames

end OAI
