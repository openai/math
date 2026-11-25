import OAI.Hierarchy.ProbeCoreWalks

namespace OAI
/-! # Fixed site-local seats of the forward payload, altimeter and reserve word paths -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.WordSeats

open AdaptiveProbe
open scoped Classical

variable {h d k : ℕ} (π : Equiv.Perm (Fin (2^h)))

abbrev Payload (h d : ℕ) := Fin (2^h) × Fin (PayloadStrip.edgeCount (Stages h d)+1)
abbrev Alt (h d k : ℕ) := ((Fin (2^h) × StageAt h d) × (Fin k × Bool)) × Fin 3
abbrev Reserve (h d k : ℕ) := (Columns h d × Fin k) × Fin 3
abbrev Turn (h d k : ℕ) := Payload h d ⊕ (Alt h d k ⊕ Reserve h d k)
abbrev Label (k : ℕ) := Unit ⊕ (((Fin k × Bool) × Fin 3) ⊕ (Fin k × Fin 3))

def tileColumn (u : Fin (2^h) × StageAt h d) (side : Bool) : Columns h d :=
  .inr (.inl ⟨u.2, occupiedStagePort π u.2 (u.1,side)⟩)

theorem tileColumn_injective (side : Bool) : Function.Injective (fun u => tileColumn (d:=d) π u side) := by
  rintro ⟨p,t⟩ ⟨q,v⟩ same
  obtain ⟨rfl,ports⟩ := Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj same))
  have atPort : (p,side)=(q,side) := (occupiedStagePort π t).injective (eq_of_heq ports)
  exact Prod.ext (Prod.mk.inj atPort).1 rfl

def payloadSite (u : Payload h d) : Site h d k :=
  (payloadPlace π u.1 (Strip.column _ u.2),none)

def altSite (u : Alt h d k) : Site h d k :=
  (tileColumn π u.1.1 (decide (u.2.val≠0)),if u.2.val=2 then some u.1.2 else none)

def reserveSite (u : Reserve h d k) : Site h d k :=
  (u.1.1,if u.2.val=1 then none else some (u.1.2,decide (u.2.val=2)))

def site : Turn h d k → Site h d k := Sum.elim (payloadSite π) (Sum.elim (altSite π) reserveSite)

def label : Turn h d k → Label k :=
  Sum.elim (fun _ => .inl ()) (Sum.elim (fun u => .inr (.inl (u.1.2,u.2)))
    (fun u => .inr (.inr (u.1.2,u.2))))

/-- The public seat contains no row, permutation or variable-length offset.
The physical column recovers the missing record in a payload or altimeter turn. -/
theorem unique_seat : Function.Injective (fun u : Turn h d k => (site π u,label u)) := by
  rintro (u|u|u) (v|v|v) eq <;> have seats := congrArg Prod.snd eq <;>
    have vertices := congrArg Prod.fst eq <;>
    simp only [label,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at seats
  · have p := (payloadPlaceAll π).injective (congrArg Prod.fst vertices)
    obtain ⟨record,slot⟩ := Prod.mk.inj p
    exact congrArg Sum.inl (Prod.ext record ((Strip.column _).injective slot))
  · obtain ⟨layer,step⟩ := Prod.mk.inj seats
    have cols := congrArg Prod.fst vertices
    change tileColumn π u.1.1 (decide (u.2.val≠0)) = tileColumn π v.1.1 (decide (v.2.val≠0)) at cols
    rw [step] at cols
    exact congrArg (fun z => Sum.inr (Sum.inl z))
      (Prod.ext (Prod.ext (tileColumn_injective π _ cols) layer) step)
  · obtain ⟨axis,step⟩ := Prod.mk.inj seats
    have col : u.1.1=v.1.1 := congrArg (fun s : Site h d k=>s.1) vertices
    exact congrArg (fun z => Sum.inr (Sum.inr z)) (Prod.ext (Prod.ext col axis) step)

def ordinal : Label k → Fin (1+9*k)
  | .inl _ => ⟨0,by omega⟩
  | .inr (.inl ((i,b),j)) => ⟨1+3*(2*i.val+b.toNat)+j.val,by
      have hi:=i.isLt;have hj:=j.isLt;cases b <;> simp [Bool.toNat] <;> omega⟩
  | .inr (.inr (i,j)) => ⟨1+6*k+3*i.val+j.val,by have hi:=i.isLt;have hj:=j.isLt;omega⟩

theorem ordinal_injective : Function.Injective (ordinal (k:=k)) := by
  intro x y eq
  have value := congrArg Fin.val eq
  rcases x with x|⟨⟨i,b⟩,j⟩|⟨i,j⟩ <;> rcases y with y|⟨⟨i',b'⟩,j'⟩|⟨i',j'⟩
  all_goals try have hi := i.isLt
  all_goals try have hi' := i'.isLt
  all_goals try have hj := j.isLt
  all_goals try have hj' := j'.isLt
  all_goals try cases b
  all_goals try cases b'
  all_goals simp only [ordinal,Bool.toNat_false,Bool.toNat_true] at value
  all_goals first | omega | rfl | skip
  all_goals simp only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,and_true]
  all_goals first
    | exact Subsingleton.elim _ _
    | exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

def seat (v : Site h d k) : {u : Turn h d k // site π u = v} ↪ Fin (1+9*k) where
  toFun u := ordinal (label u.val)
  inj' := fun a b eq => Subtype.ext (unique_seat π (Prod.ext (a.property.trans b.property.symm)
    (ordinal_injective eq)))

theorem card (v : Site h d k) : Fintype.card {u : Turn h d k // site π u = v} ≤ 1+9*k := by
  simpa using Fintype.card_le_of_injective _ (seat π v).injective

@[simp] theorem alt_start (p : Fin (2^h)) (t : StageAt h d) (l : Fin k×Bool) :
    altSite π (((p,t),l),0) = (commodityEnds π (.inr ((p,t),l))).1 := rfl

@[simp] theorem alt_middle (p : Fin (2^h)) (t : StageAt h d) (l : Fin k×Bool) :
    altSite π (((p,t),l),1) =
      (outputCol t ((advisedStage h d π t).group p) ((advisedStage h d π t).output p),none) := rfl

@[simp] theorem alt_end (p : Fin (2^h)) (t : StageAt h d) (l : Fin k×Bool) :
    altSite π (((p,t),l),2) = (commodityEnds π (.inr ((p,t),l))).2 := rfl

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
