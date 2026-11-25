import OAI.Hierarchy.DescentMaterialActorInputs

namespace OAI
/-! The physically padded old host array agrees on real hosts and suppresses all actors on ghost hosts. -/
namespace Hierarchy.DescentScalarVenueMask.Stage
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentSixParty
open DescentPackedColony DescentGroupPeerOrder
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {d k age a short H K Z : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {price ε : ℝ}
variable (groups : J↪Fin Z) (hosts : V↪Fin H) (pad : Fin H↪Fin K)
omit [DecidableEq V] [DecidableEq J] in
private theorem orig {β : Type*} (empty : β) (x : J×V→β) (h : Fin H) (g : Fin Z) :
    Prepare.spreadField groups (hosts.trans pad) empty x (pad h) g=Prepare.spreadField groups hosts empty x h g :=by
  by_cases occupied:∃t:J×V,groups t.1=g ∧ hosts t.2=h
  · obtain ⟨t,hg,hh⟩:=occupied
    have left:∃v:J×V,groups v.1=g ∧ (hosts.trans pad) v.2=pad h:=⟨t,hg,congrArg pad hh⟩
    have right:∃v:J×V,groups v.1=g ∧ hosts v.2=h:=⟨t,hg,hh⟩
    rw [Prepare.spreadField,Prepare.spreadField,dite_eq_left left,dite_eq_left right]
    exact congrArg x (Prod.ext (groups.injective (left.choose_spec.1.trans right.choose_spec.1.symm))
      (hosts.injective ((pad.injective left.choose_spec.2).trans right.choose_spec.2.symm)))
  · have no:¬∃v:J×V,groups v.1=g ∧ (hosts.trans pad) v.2=pad h:=by
      rintro ⟨v,hh,hp⟩;exact occupied ⟨v,hh,pad.injective hp⟩
    simp only [Prepare.spreadField,dite_eq_right occupied,dite_eq_right no]
variable (A : GroupStage W T price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S age) (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (profile : ℕ) (lay : Bool)
local notation "t" => tokens (short:=short) A native S ready rank win profile lay groups
theorem tokens_padded (slots : ℕ) (x : Fin (2^k)) (j : Fin (1+A.cap*6)) (h : Fin H) (g : Fin Z) :
    t (hosts.trans pad) slots x j (pad h) g=t hosts slots x j h g :=by
  simp only [tokens,Prepare.actors,orig groups hosts pad]

theorem tokens_absent (slots : ℕ) (x : Fin (2^k)) (j : Fin (1+A.cap*6)) (h : Fin K) (g : Fin Z)
    (hole : ∀v,pad v≠h) : t (hosts.trans pad) slots x j h g=none :=by
  have empty:¬∃v:J×V,groups v.1=g ∧ (hosts.trans pad) v.2=h:=by
    rintro ⟨z,_,hh⟩;exact hole (hosts z.2) hh
  have zero (a n : ℕ) : (encode a n).symm (0:Cell (a*n))=fun _=>0:=by
    apply (encode a n).symm_apply_eq.mpr
    apply Fin.ext
    change 0=(finFunctionFinEquiv (fun _:Fin n=>(0:Cell a))).val
    simp
  simp only [tokens,Prepare.actors,Prepare.spreadField,dite_eq_right empty,Publisher.ticket]
  cases y:finSumFinEquiv.symm j with
  | inl u=>simp [oldTicket,zero]
  | inr u=>simp [newTicket,zero]

theorem hub_padded (h : Fin H) :
    Census.hub A (hosts.trans pad) (pad h)=Census.hub A hosts h :=by
  by_cases present:∃v,hosts v=h
  · have hp:∃v,(hosts.trans pad) v=pad h:=⟨present.choose,congrArg pad present.choose_spec⟩
    have same:hp.choose=present.choose:=hosts.injective ((pad.injective hp.choose_spec).trans present.choose_spec.symm)
    rw [Census.hub,Census.hub,dite_eq_left hp,dite_eq_left present,same]
  · have disappear:¬∃v,(hosts.trans pad) v=pad h:=by rintro ⟨v,hv⟩;exact present ⟨v,pad.injective hv⟩
    simp only [Census.hub,dite_eq_right present,dite_eq_right disappear]

end
end Hierarchy.DescentScalarVenueMask.Stage

end OAI
