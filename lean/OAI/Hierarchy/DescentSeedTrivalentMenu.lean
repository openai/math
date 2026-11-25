import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Tactic

namespace OAI
/-! # The table rows of the original trivalent graph and their eight local selectors -/
namespace Hierarchy
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
namespace DescentInitialHost
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} [Fintype P] {b : P→ℕ}
variable (N : Network D P b)

abbrev Pattern (v : N.Site) :=
  (∀ e : {e // N.src e=v ∨ N.dst e=v},Fin (N.width e.1) → Bool) ×
  (∀ p : {p // N.attach p=v},Fin (b p.1) → Bool)

def coeff (T : N.Tables F) (v : N.Site) (p : Pattern N v) := T v p.1 p.2

end DescentInitialHost
namespace DescentPhysicalSplit
variable {D : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)

abbrev Leg := P ⊕ (N.Edge × Bool)
def owner : Leg N → N.Site
  | .inl p => N.attach p
  | .inr (e,b) => if b then N.dst e else N.src e

abbrev Fibre (v : N.Site) := {p : Leg N // owner N p=v}
def count (v : N.Site) := Fintype.card (Fibre N v)
theorem count_eq_degree (v : N.Site) : count N v=N.bitDegree v := by
  rw [count,show Fintype.card (Fibre N v)=(Finset.univ.filter (fun p=>owner N p=v)).card
    from Fintype.card_subtype _]
  unfold Network.bitDegree
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rcases p with p|⟨e,s⟩ <;> rfl

end DescentPhysicalSplit
namespace DescentInitialHost
open DescentPhysicalSplit
variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))

/-- Read one genuine bit on each oriented incident leg, hence both ends of
a loop read its same bit. This embeds all distinct local patterns. -/
def legPattern (single : ∀e,N.width e=1) (v : N.Site) :
    Pattern N v ↪ (Fibre N v→Bool) where
  toFun pat
    | ⟨.inl p,h⟩ => pat.2 ⟨p,h⟩ 0
    | ⟨.inr (e,false),h⟩ => pat.1 ⟨e,Or.inl h⟩ ⟨0,by rw [single];decide⟩
    | ⟨.inr (e,true),h⟩ => pat.1 ⟨e,Or.inr h⟩ ⟨0,by rw [single];decide⟩
  inj' := by
    intro p q eqn
    apply Prod.ext
    · funext e j
      have ix : j=(⟨0,by rw [single];decide⟩ : Fin (N.width e.val)) := Fin.ext (by
        change j.val=0
        have bound : j.val<1 := j.isLt.trans_le (single e.val).le
        omega)
      rw [ix]
      rcases e.property with src|dst
      · exact congrFun eqn ⟨.inr (e.val,false),src⟩
      · exact congrFun eqn ⟨.inr (e.val,true),dst⟩
    · funext p j
      obtain rfl : j=0 := Subsingleton.elim _ _
      exact congrFun eqn ⟨.inl p.val,p.property⟩

theorem patterns_le_eight (tri : N.Trivalent) (v : N.Site) : Fintype.card (Pattern N v)≤8 := by
  have inject := Fintype.card_le_of_embedding (legPattern N tri.1 v)
  rw [Fintype.card_fun,Fintype.card_bool,←count,count_eq_degree] at inject
  exact inject.trans (Nat.pow_le_pow_right (by decide : 0<2) (tri.2 v))

end DescentInitialHost
end
end Hierarchy

end OAI
