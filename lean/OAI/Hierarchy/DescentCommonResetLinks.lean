import OAI.Hierarchy.DescentCanonicalFallback
import OAI.Hierarchy.DescentGoodPortCoherence

namespace OAI
/-! # Directed socket mates for the actual shared reset host -/

namespace Hierarchy.DescentChosenRouter
open DescentRouterSlots DescentCanonicalPorts
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n : ℕ}
variable (P : Placement V I H A k (2^n))
local notation "seen" => Seen P.b P.depth P.L P.keys P.hub P.old P.fall

/-- The concrete fallback input at the left or right end of the observed cable. -/
def fallEnd (s : Bool) (c : seen) : H := if s then c.val.2 else c.val.1
def fallLeg (s : Bool) (c : seen) : LinkId P.owner s (.inr (fallEnd P s c)) :=
  ⟨.inr c,by cases s <;> rfl⟩

theorem opposite_fallLeg (s : Bool) (c : seen) :
    opposite P s _ (fallLeg P s c)=fallEnd P (!s) c := by cases s <;> rfl

variable {Z : Type*} (label : H→Z)
def fallSocket (s : Bool) (c : seen) : Z×List Bool :=
  (label (fallEnd P s c),List.ofFn ((P.fallbackBook s _).codes (fallLeg P s c)))

/-- Both the name and the leaf digits of the incoming socket determine both
coordinates of the remote socket, even across distinct coarse blocks. -/
theorem fallSocket_peer (book : P.CommonFallback label) (s : Bool) {c d : seen}
    (eqn : fallSocket P label s c=fallSocket P label s d) :
    fallSocket P label (!s) c=fallSocket P label (!s) d := by
  have roots : label (fallEnd P s c) = label (fallEnd P s d) := by
    simpa only [fallSocket] using congrArg Prod.fst eqn
  have digits := congrArg Prod.snd eqn
  have other := (book.2 s _ _ roots (fallLeg P s c) (fallLeg P s d)).mp digits
  rw [opposite_fallLeg,opposite_fallLeg] at other
  apply Prod.ext other
  apply (book.2 (!s) _ _ other (fallLeg P (!s) c) (fallLeg P (!s) d)).mpr
  simpa only [opposite_fallLeg,Bool.not_not] using roots

/-- Socket identity before joining either the actual reserved rotor cable or
the cable joining two concrete leaves of the fallback trees. -/
def linkSocket (m : ℕ) (s : Bool) : P.Contact→(((V×ℕ)×Fin (2^n)) ⊕ (Z×List Bool))
  | .inl c => .inl (P.outputName m s c)
  | .inr c => .inr (fallSocket P label s c)

theorem linkSocket_peer (m : ℕ) (rotors : P.CommonOutputs m) (book : P.CommonFallback label)
    (s : Bool) (c d : P.Contact) (eqn : linkSocket P label m s c=linkSocket P label m s d) :
    linkSocket P label m (!s) c=linkSocket P label m (!s) d := by
  rcases c with c|c <;> rcases d with d|d
  · exact congrArg Sum.inl (rotors s c d (Sum.inl.inj eqn))
  · exact False.elim (by simp only [linkSocket, Sum.inl_ne_inr] at eqn)
  · exact False.elim (by simp only [linkSocket, Sum.inr_ne_inl] at eqn)
  · exact congrArg Sum.inr (fallSocket_peer P label book s (Sum.inr.inj eqn))

/-- The decoded partial socket map is independent of every chosen witness. -/
def linkPeer (m : ℕ) (s : Bool) (z : ((V×ℕ)×Fin (2^n)) ⊕ (Z×List Bool)) :=
  if hit : ∃c,linkSocket P label m s c=z then some (linkSocket P label m (!s) hit.choose) else none

theorem linkPeer_at (m : ℕ) (rotors : P.CommonOutputs m) (book : P.CommonFallback label)
    (s : Bool) (c : P.Contact) :
    linkPeer P label m s (linkSocket P label m s c)=some (linkSocket P label m (!s) c) := by
  have hit : ∃d,linkSocket P label m s d=linkSocket P label m s c := ⟨c,rfl⟩
  rw [linkPeer,dite_eq_left hit]
  exact congrArg some (linkSocket_peer P label m rotors book s _ _ hit.choose_spec)

end
end Hierarchy.DescentChosenRouter

end OAI
