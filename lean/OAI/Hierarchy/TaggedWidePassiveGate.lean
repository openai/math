import OAI.Hierarchy.TaggedWidePassiveRows
import OAI.Hierarchy.TaggedWideOverlapNative

namespace OAI
/-! # Fixed site circuit for the passive part of the actual signed product table -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open ThreeFlat Routing LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {F V P I J : Type} [Field F] [Fintype V] [Fintype I] [Fintype J] {W : ℕ}
private abbrev Pins (w : ℕ) := BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits w) (BinaryBarrelTurns.digits w) w

def circuit (read : I×J → Pins W → V⊕Bool) : BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (F:=F) (I:=I×J) (V:=V) (A:=fun _=>Pins W) (fun _=>BinaryBarrelTurns.fixed F W) read

theorem cost (read : I×J → Pins W → V⊕Bool) : (circuit (F:=F) read).cells+(circuit (F:=F) read).internal≤
    Fintype.card I*Fintype.card J*(2308*W*(W.log2+2)) := by
  rw [circuit,WideHost.localFamily_size]
  calc
    _ ≤ ∑ _ : I×J,2308*W*(W.log2+2) := Finset.sum_le_sum fun _ _=>BinaryBarrelTurns.fixed_size F W
    _ = Fintype.card I*Fintype.card J*(2308*W*(W.log2+2)) := by simp [Fintype.card_prod]

variable (read : I×J → Pins W → V⊕Bool)
variable (pass old new : P→ℕ) (l : Parts P I W fun p=>pass p+old p) (r : Parts P J W fun p=>pass p+new p)
variable (x : I → Bits W) (y : J → Bits W) (a b : P→ℕ → Bool)

def linked (i : I) (j : J) := decide (∃p,l.owner i=some p ∧ r.owner j=some p)

theorem eval (v : V → Bool)
    (source : ∀i p,l.owner i=some p→∀u : Fin (l.width i),x i (u.castLE (l.within i))=a p (l.base i+u.val))
    (target : ∀j p,r.owner j=some p→∀u : Fin (r.width j),y j (u.castLE (r.within j))=b p (r.base j+u.val))
    (pins : ∀i j,let L := l.view old i; let R := r.view new j
      (Sum.elim v id) ∘ read (i,j)=BinaryBarrelTurns.pins
        ((addressEquiv _).symm (BinaryBarrelTurns.address (header W L R (linked pass old new l r i j))))
        (fun s=>(addressEquiv _).symm (BinaryBarrelTurns.address (heads W L R s))) (data (x i) (y j))) :
    TypedWiring.value (circuit (F:=F) read) v=
      if ∀p (u : Fin (pass p)),a p (u.val+old p)=b p (u.val+new p) then 1 else 0 := by
  rw [circuit,WideHost.localFamily_eval]
  let test (q : I×J) := ∀t (u : Fin (l.width q.1)) (v : Fin (r.width q.2)),∀p,
    l.owner q.1=some p → r.owner q.2=some p → l.base q.1+u.val=t+old p → r.base q.2+v.val=t+new p→
      x q.1 (u.castLE (l.within q.1))=y q.2 (v.castLE (r.within q.2))
  have point (q : I×J) : TypedWiring.value (BinaryBarrelTurns.fixed F W) ((Sum.elim v id) ∘ read q)=
      if test q then 1 else 0 := by
    rcases q with ⟨i,j⟩
    rw [pins,value (l.view old i) (r.view new j) _ (l.within i) (r.within j)]
    apply ite_congr ?_ (fun _=>rfl) (fun _=>rfl)
    apply propext
    constructor
    · intro eqn t u w p hi hj atL atR
      have hit : linked pass old new l r i j=true := decide_eq_true ⟨p,hi,hj⟩
      exact eqn t u w hit (by simpa [Parts.view,hi] using atL) (by simpa [Parts.view,hj] using atR)
    · intro eqn t u w hit atL atR
      obtain ⟨p,hi,hj⟩ : ∃p,l.owner i=some p ∧ r.owner j=some p := of_decide_eq_true hit
      exact eqn t u w p hi hj (by simpa [Parts.view,hi] using atL) (by simpa [Parts.view,hj] using atR)
  simp_rw [point]
  rw [Fintype.prod_boole]
  have same : (∀q,test q) ↔ ∀p (u : Fin (pass p)),a p (u.val+old p)=b p (u.val+new p) := by
    rw [←passive_iff pass old new l r x y a b source target]
    exact ⟨fun h i j=>h (i,j),fun h ⟨i,j⟩=>h i j⟩
  simp only [same]

end Hierarchy.Tagged.PassiveWindow

end
end OAI
