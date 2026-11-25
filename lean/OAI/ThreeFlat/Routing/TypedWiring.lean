import OAI.ThreeFlat.BitNetworkGlue
import OAI.ThreeFlat.LocalTableNetwork

namespace OAI
/-! # Bit networks with finite pin labels

Finite pin labels identify record and slot positions.  This interface uses
the same `BitNetwork` tables and internal bits as the numbered network.
-/

namespace ThreeFlat.Routing

open scoped BigOperators Classical

namespace TypedWiring

noncomputable section
variable {F : Type*} {P : Type*} [Fintype P]

/-- Contraction with the external pins indexed by a finite type. -/
def value [CommSemiring F] (N : BitNetwork F (Fintype.card P)) (pin : P → Bool) : F :=
  N.eval fun i => pin ((Fintype.equivFin P).symm i)

/-- A finite Boolean table of bounded arity with arbitrary field values. -/
def localTable [Zero F] [One F] (φ : (P → Bool) → F) : BitNetwork F (Fintype.card P) :=
  TableCompiler.localTableNetwork fun b => φ (fun i => b (Fintype.equivFin P i))

theorem localTable_value [CommSemiring F] (φ : (P → Bool) → F) (x : P → Bool) :
    value (localTable φ) x = φ x := by
  unfold value localTable
  rw [TableCompiler.localTableNetwork_eval]
  simp

variable {I H : Type*} [Fintype I] [Fintype H] {port : I → Type*}
  [∀ i, Fintype (port i)]
  (N : (i : I) → BitNetwork F (Fintype.card (port i)))
  (wire : (i : I) → port i → P ⊕ H)

private def numberedWire (i : I) (k : Fin (Fintype.card (port i))) :
    BitSource (Fintype.card H) (Fintype.card P) :=
  match wire i ((Fintype.equivFin _).symm k) with
  | .inl p => .pin (Fintype.equivFin _ p)
  | .inr h => .hidden (Fintype.equivFin _ h)

def glue : BitNetwork F (Fintype.card P) :=
  BitNetwork.glue N (numberedWire wire)

@[simp] theorem glue_cells : (glue N wire).cells = ∑ i, (N i).cells := BitNetwork.glue_cells ..
@[simp] theorem glue_internal : (glue N wire).internal = Fintype.card H + ∑ i, (N i).internal :=
  BitNetwork.glue_internal ..

theorem glue_value [CommSemiring F] (x : P → Bool) :
    value (glue N wire) x =
      ∑ h : H → Bool, ∏ i, value (N i) (fun k => Sum.elim x h (wire i k)) := by
  unfold value glue
  rw [BitNetwork.glue_eval]
  symm
  let e := Equiv.arrowCongr (Fintype.equivFin H) (Equiv.refl Bool)
  apply Fintype.sum_equiv e
  intro h
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext k
  dsimp only [numberedWire]
  cases wire i ((Fintype.equivFin (port i)).symm k) with
  | inl z => simp [BitSource.read]
  | inr z => simp [BitSource.read, e, Equiv.arrowCongr]

end
end TypedWiring
end ThreeFlat.Routing

end OAI
