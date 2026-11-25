import OAI.Computability.NearSquareRoot.CRTTableArithmetic
import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import Mathlib.Tactic

/-! # Prescribing the controls and sparse targets of a prepared switch stage

A prepared address, written most significant segment first, has the form
`high, prefix, Y, Z, low`. Both sparse chunks have `(b+1)*G` bits, including the final padding group. Target `q`
is at offset `(b-1-q)*G` in Y because the physical queue reads the
groups in reverse order. All positions in this module are little endian.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Code

def targetOffset (b G low q : ℕ) := low+(b+1)*G+(b-1-q)*G
def controlOffset (b G low j : ℕ) := low+2*((b+1)*G)+j

/-- Addresses in the prepared word, in target metadata order. -/
def targetPos {k b c G low : ℕ} (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k)
    (q : Fin b) : Fin k :=
  ⟨targetOffset b G low q.val, by
    have h := Nat.mul_lt_mul_of_pos_right (show b-1-q.val < b+1 by omega) pos
    dsimp [targetOffset]
    omega⟩

def controlPos {k b c G low : ℕ} (fit : low+2*((b+1)*G)+c ≤ k) (j : Fin c) : Fin k :=
  ⟨controlOffset b G low j.val, by dsimp [controlOffset]; omega⟩

variable {k b c G low : ℕ}

theorem targetPos_injective (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) :
    Function.Injective (targetPos pos fit : Fin b → Fin k) := by
  intro x y e
  have h := congrArg Fin.val e
  change low+(b+1)*G+(b-1-x.val)*G = low+(b+1)*G+(b-1-y.val)*G at h
  have e' : (b-1-x.val)*G = (b-1-y.val)*G := Nat.add_left_cancel h
  rw [Nat.mul_left_inj pos.ne'] at e'
  apply Fin.ext
  omega

theorem controlPos_injective (fit : low+2*((b+1)*G)+c ≤ k) :
    Function.Injective (controlPos fit : Fin c → Fin k) := by
  intro x y e
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))

theorem positions_disjoint (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) (x : Fin b) (y : Fin c) :
    targetPos pos fit x ≠ controlPos fit y := by
  intro eq
  have e := congrArg Fin.val eq
  change low+(b+1)*G+(b-1-x.val)*G = low+2*((b+1)*G)+y.val at e
  have := Nat.mul_lt_mul_of_pos_right (show b-1-x.val < b+1 by omega) pos
  omega

def pairs (targets : Fin b → Fin k) (controls : Fin c → Fin k)
    (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) : List (Fin k × Fin k) :=
  (List.ofFn fun q => (targetPos pos fit q,targets q)) ++
  (List.ofFn fun j => (controlPos fit j,controls j))

theorem dest_nodup (targets : Fin b → Fin k) (controls : Fin c → Fin k)
    (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) :
    ((pairs targets controls pos fit).map Prod.fst).Nodup := by
  simp only [pairs, List.map_append,List.map_ofFn,Function.comp_def,List.nodup_append,
    List.nodup_ofFn, List.mem_ofFn]
  refine ⟨targetPos_injective pos fit,controlPos_injective fit,?_⟩
  intro a ha v hv
  obtain ⟨q,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hv
  exact positions_disjoint pos fit q j

theorem src_nodup {targets : Fin b → Fin k} {controls : Fin c → Fin k}
    (ht : Function.Injective targets) (hc : Function.Injective controls)
    (hd : ∀ q j, targets q ≠ controls j) (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) :
    ((pairs targets controls pos fit).map Prod.snd).Nodup := by
  simp only [pairs, List.map_append,List.map_ofFn,Function.comp_def,List.nodup_append,
    List.nodup_ofFn, List.mem_ofFn]
  refine ⟨ht,hc,?_⟩
  intro a ha v hv
  obtain ⟨q,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hv
  exact hd q j

end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
