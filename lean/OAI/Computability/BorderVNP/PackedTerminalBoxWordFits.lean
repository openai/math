import OAI.Computability.BorderVNP.PackedHistoryBoxVolume
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryLiteralFits
import OAI.Computability.BorderVNP.PackedBankPacketFields

/-! # Numerical literals of the signed processor's public terminal boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Cover BorderVNP.Epoch Shortening Packing Packing.Inherited CellSparse
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open CellPacketGeometry CellPacketGeometry.SiteWords
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {start T : ℕ}
    (dir : Directory.Layout) (count : dir.entries=(fan S)^T*dir.sites) (number : e.Entry → ℕ)
    (pos : 0<(SelectedSchedule.boundaryShape S start T).sites)

/-- All publicly emitted scalar words fit. The only field-dependent entries
are the actual numerical identifiers of paid factors. Opaque original boxes
contribute no public data. -/
theorem scheduledBoxes_literal_words {w : ℕ} (known : BoxRoster.paidWordLimit e < 2^w)
    (three : 3 < 2^w) (ids : ∀ t, number t < 2^w)
    (i : Fin (SelectedSchedule.boundaryShape S start T).sites) :
    ∀ n ∈ boxWords (scheduledBoxes dir count number pos i), n < 2^w := by
  apply known_words_fit _ (bound := 2^w-1) (by omega) three
  intro fs member
  rcases scheduledBoxes_cases dir count number pos i with hx | ⟨a,v,hx⟩ | ⟨j,hx⟩
  · simp [hx] at member
  · rw [hx,List.mem_singleton,Sum.inl.injEq] at member
    subst fs
    refine ⟨by simp; omega,?_⟩
    intro f hf
    rw [List.mem_singleton] at hf
    subst f
    have h := (Finset.le_sup (s := Finset.univ)
      (f := fun z : (e.net a).Site => (3+PaidBox.arity e a z+2^PaidBox.arity e a z)+1)
      (Finset.mem_univ v)).trans (Finset.le_sup (s := Finset.univ) (f := fun b : Fin e.count =>
        Finset.univ.sup fun z : (e.net b).Site => (3+PaidBox.arity e b z+2^PaidBox.arity e b z)+1)
        (Finset.mem_univ a))
    change 3+PaidBox.arity e a v+2^PaidBox.arity e a v+1 ≤ BoxRoster.paidWordLimit e at h
    let arity := PaidBox.arity e a v
    have hdim : arity ≤ 3+arity+2^arity+1 :=
      ((Nat.le_add_left arity 3).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    have hsize : 2^arity ≤ 3+arity+2^arity+1 := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    have limit : BoxRoster.paidWordLimit e ≤ 2^w-1 := by omega
    exact BankCharges.paid_factorFields e number a v _ ((hdim.trans h).trans limit) ((hsize.trans h).trans limit)
      (fun t => by have := ids t; omega)
  · simp [hx] at member

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
