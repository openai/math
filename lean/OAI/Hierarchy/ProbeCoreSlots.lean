import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.ProbeStageWidthRatio

namespace OAI
/-! # The fixed communication slots for the core links -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical
noncomputable section

variable {S : PurchaseSampler} {h d k : ℕ}

abbrev Groups (S : PurchaseSampler) (h d k : ℕ) :=
  Free S h d k ⊕ (Σ t : StageAt h d,(stageAt h d t).Group × ColumnLayer k)

def ports : Groups S h d k → Type
  | .inl _ => Bool
  | .inr ⟨t,_,_⟩ => Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span

instance (g : Groups S h d k) : Fintype (ports g) := by
  rcases g with f|⟨t,g,l⟩ <;> dsimp [ports] <;> infer_instance

abbrev Socket (S : PurchaseSampler) (h d k : ℕ) := (g : Groups S h d k) × ports g

def socketSite : Socket S h d k → Site h d k
  | ⟨.inl f,false⟩ => (freeEnds f).1
  | ⟨.inl f,true⟩ => (freeEnds f).2
  | ⟨.inr ⟨t,g,l⟩,i⟩ => (.inr (.inl ⟨t,g,i⟩),l)

def socketUse (π : Equiv.Perm (Fin (2^h))) : Edges S h d k × Bool → Socket S h d k
  | (.inl f,s) => ⟨.inl f,s⟩
  | (.inr ((p,t),l),s) =>
    let port := occupiedStagePort π t (p,s)
    ⟨.inr ⟨t,port.1,l⟩,port.2⟩

private def socketKey : Socket S h d k → (Free S h d k × Bool) ⊕ (StageColumns h d × ColumnLayer k)
  | ⟨.inl f,s⟩ => .inl (f,s)
  | ⟨.inr ⟨t,g,l⟩,i⟩ => .inr (⟨t,g,i⟩,l)

/-- Each physical socket is used by at most one end of the entire term's
core catalogue. Unoccupied ports remain in the same public positive-scale groups. -/
theorem unique_socket (π : Equiv.Perm (Fin (2^h))) :
    Function.Injective (socketUse (S:=S) (d:=d) (k:=k) π) := by
  rintro ⟨e,s⟩ ⟨f,u⟩ eq
  have key := congrArg (socketKey (S:=S) (h:=h) (d:=d) (k:=k)) eq
  rcases e with e|⟨⟨p,t⟩,l⟩ <;> rcases f with f|⟨⟨q,t'⟩,l'⟩
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inl.inj key)
    rfl
  · exact (Sum.inl_ne_inr key).elim
  · exact (Sum.inr_ne_inl key).elim
  · have pair := Sum.inr.inj key
    have tags := congrArg Prod.fst pair
    obtain ⟨rfl,physical⟩ := Sigma.mk.inj_iff.mp tags
    have eq := (occupiedStagePort π t).injective (eq_of_heq physical)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have ll : l=l' := congrArg Prod.snd pair
    subst l';rfl

theorem socket_ends (π : Equiv.Perm (Fin (2^h))) (e : Edges S h d k) :
    socketSite (socketUse π (e,false))=(ends π e).1 ∧
    socketSite (socketUse π (e,true))=(ends π e).2 ∧
    (socketUse π (e,false)).1=(socketUse π (e,true)).1 := by
  rcases e with f|⟨⟨p,t⟩,l⟩
  · exact ⟨rfl,rfl,rfl⟩
  · simp [socketUse,socketSite,ends,inputCol,outputCol]

theorem private_group (f : Free S h d k) : Fintype.card (ports (Sum.inl f : Groups S h d k))=2 := by
  change Fintype.card Bool=2;decide

theorem stage_group (t : StageAt h d) (g : (stageAt h d t).Group) (l : ColumnLayer k) :
    Fintype.card (ports (Sum.inr ⟨t,g,l⟩ : Groups S h d k))=2*(stageAt h d t).span := by
  change Fintype.card (Fin _ ⊕ Fin _)=_
  simp [two_mul]

/-- The public exponent superAddress has ratio 2^-W by superAddress_ratio.
One spare address bit suffices for the two sides of every native group. -/
theorem positive_group_bound (W : ℕ) (t : StageAt h (2^W))
    (g : (stageAt h (2^W) t).Group) (l : ColumnLayer k) :
    Fintype.card (ports (Sum.inr ⟨t,g,l⟩ : Groups S h (2^W) k))≤2^superAddress W 1 h := by
  rw [stage_group]
  have shape := template_dyadic (h:=h) (d:=2^W) (Nat.two_pow_pos W) (stageAt h (2^W) t)
    (List.get_mem (permutationFabric h (2^W)).shapes t)
  rcases shape.1 with outer|central
  · rw [outer,Nat.mul_comm,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) (outer_address_fits W 1 h)
  · rw [central,Nat.mul_comm,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) (center_address_fits W 1 h)

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
