import OAI.Hierarchy.DescentPhysicalDegree
import OAI.Hierarchy.DescentRotorNetwork

namespace OAI
/-! # The physical configured rotor with all private path cables present -/

namespace Hierarchy.DescentRotor.Physical
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open DescentBaseProfile DescentPhysicalSplit Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {n h D C w u R : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "N" => host G.arcs D R C w u

/-- The physical incidence at a row consists of its two named terminals and
the individual directed host half edges, including both ends of each loop. -/
def rowFibre (v : Fin (2^n)) : Fibre N v ≃ Slot G.arcs v where
  toFun
    | ⟨.inl q,_⟩ => .inl q.2
    | ⟨.inr ⟨e,b⟩,hit⟩ => .inr ⟨(e,b),by cases b <;> exact hit⟩
  invFun
    | .inl b => ⟨.inl (v,b),rfl⟩
    | .inr p => ⟨.inr p.val,by rcases p with ⟨⟨e,(_|_)⟩,hit⟩ <;> exact hit⟩
  left_inv := by
    rintro ⟨⟨v',b⟩|⟨e,b⟩,hit⟩
    · change v'=v at hit
      subst v'
      rfl
    · rfl
  right_inv := by rintro (b|⟨⟨e,b⟩,hit⟩) <;> rfl

private theorem local_legs (v : Fin (2^n)) (p : Fibre N v) :
    width N p.val=R*(u*SlotWidth G.arcs C w v (rowFibre G v p)) := by
  rcases p with ⟨⟨j,b⟩|⟨e,b⟩,h⟩ <;> rfl

private theorem row_price (v : Fin (2^n)) :
    (count N v+2)*∑i,localWidth N v i =
      R*Attachment.bitCost (fun i=>SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i)) u := by
  have sz : count N v=Fintype.card (Slot G.arcs v) := Fintype.card_congr (rowFibre G v)
  have left : (∑i,localWidth N v i)=(∑p : Fibre N v, width N p.val) :=
    (index N v).symm.sum_comp (fun p=>width N p.val)
  rw [left,sz,Attachment.bitCost_eq]
  simp_rw [local_legs]
  rw [(rowFibre G v).sum_comp (fun s=>R*(u*SlotWidth G.arcs C w v s)),
    (Fintype.equivFin (Slot G.arcs v)).symm.sum_comp (SlotWidth G.arcs C w v),
    ←Finset.mul_sum,←Finset.mul_sum]
  ring

theorem physical_width :
    (∑e,(graph N).width e)+(∑_q : Pin (2^n),R*(u*w)) ≤
      R*(∑v, Attachment.bitCost
        (fun i=>SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i)) u) := by
  apply (total_le N).trans_eq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => row_price (D:=D) (R:=R) (C:=C) (w:=w) (u:=u) G v

variable {K E : Type*} [Field K] [Fintype E] {hw : 0<w}
    {src dst : E→Fin (2^n)} {pay : ℝ}
variable (P : BaseCircuit K G C w u hw src dst pay)

/-- Parallel layer and payload multiplicities change cable widths, keeping
the same fixed collection of physical taps at every host row. -/
def rotor (D : ℕ) := graph (host G.arcs D P.layers C w u)
def rotorTables (D : ℕ) := tables (host G.arcs D P.layers C w u) (hostTables G.arcs P.tables)

theorem rotor_value (x y : E→Fin u→Bool) :
    (rotor G P D).value (rotorTables G P D) (actualPins P x y) =
      if ∀e,x e=y e then 1 else 0 :=
  (value_eq _ _ _).trans (actual_value (D:=D) P x y)

theorem rotor_degree (v : (rotor G P D).Site) : (rotor G P D).bitDegree v≤3 := degree _ v

theorem rotor_sites : Fintype.card (rotor G P D).Site=(2*h+4)*2^n := by
  rw [rotor,site_count]
  have size (v) : count (host G.arcs D P.layers C w u) v=2*h+2 := by
    refine (Fintype.card_congr (rowFibre G v)).trans ?_
    refine Eq.trans ?_ (regular_slots G v)
    exact congrArg (@Fintype.card (Slot G.arcs v)) (Subsingleton.elim _ _)
  calc
    _ = ∑ _v : Fin (2^n), ((2*h+2)+2) :=
      Finset.sum_congr rfl fun v _ => congrArg (· + 2) (size v)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      ring

/-- The actual integer wire count includes every private spine edge and all
exposed row pin widths. Its coefficient is independent of the number of rows. -/
theorem rotor_price :
    (((∑e,(rotor G P D).width e)+(∑_q : Pin (2^n),P.layers*(u*w)):ℕ):ℝ) ≤
      21*((2*h+4)*(2*h*C+2):ℕ)*pay := by
  have bound := physical_width (D:=D) (R:=P.layers) (C:=C) (w:=w) (u:=u) G
  exact (Nat.cast_le.mpr bound).trans P.bitCost

end
end Hierarchy.DescentRotor.Physical

end OAI
