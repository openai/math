import OAI.Hierarchy.GridThroughPinCore
import OAI.Hierarchy.FactorPinIntervals

namespace OAI
/-! # Placing original labelled endpoints and advice bits at a selector tick -/

namespace Hierarchy.GridThrough.PinAssignment

open FactorPinIntervals
open scoped Classical
noncomputable section

variable {E : Type} {S N k n q d : ℕ}

variable (P : Layout (Cell k n × Fin q) S N d) (direction : E → Fin k) (port : E × Bool ↪ Fin S)
    (paired : ∀ e, P.origin (port (e,true))=P.origin (port (e,false)))

include paired in
private theorem tick_side (u : E × Bool) : P.tick (port (u.1,false)) = P.tick (port u) := by
  rcases u with ⟨e, s⟩
  cases s with
  | false => rfl
  | true => exact congrArg P.owner (paired e).symm

/-- The original factor interval determines both endpoint addresses. Fixed input
bits are installed from the original advice tape, and the extra header comes first. -/
def ofFactorIntervals : PinAssignment E k n q d where
  direction := direction
  tick e := P.tick (port (e,false))
  slot u := P.slot (port u)
  fresh := by
    intro u v eqn
    have tEq := congrArg Prod.fst eqn
    have sEq := congrArg Prod.snd eqn
    apply port.injective
    apply P.address.injective
    exact Prod.ext ((tick_side P port paired u).symm.trans (tEq.trans (tick_side P port paired v))) sEq
  literal ci :=
    let replica := finProdFinEquiv.symm ci.2
    P.literal (ci.1,replica.1) replica.2


theorem ofFactorIntervals_slot (u : E × Bool) :
    ((ofFactorIntervals P direction port paired).slot u).val = (P.header (P.tick (port u))).length +
      (P.inputBits (P.tick (port u))).idxOf (port u) := rfl

theorem ofFactorIntervals_endpoint (u : E × Bool) :
    let t := P.tick (port u)
    let touch : Touch (ofFactorIntervals P direction port paired).touch := ⟨(u.1, ((ofFactorIntervals P direction port paired).row u.1) (direction u.1)),rfl⟩
    (ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,P.slot (port u))) = .inl (touch,u.2) := by
  apply (pinSource_inl ..).mpr
  have eqn := tick_side P port paired u
  apply Prod.ext
  · change (P.tick (port (u.1,false))).1 = (P.tick (port u)).1
    exact congrArg (fun t : Cell k n × Fin q => t.1) eqn
  · change finProdFinEquiv ((P.tick (port (u.1,false))).2,P.slot (port (u.1,u.2)))=_
    rw [eqn]

private theorem exact_source {t : (Cell k n × Fin q)} {i : Fin d} (u : Touch (ofFactorIntervals P direction port paired).touch × Bool)
    (eqn : (ofFactorIntervals P direction port paired).dest u=(t.1,finProdFinEquiv (t.2,i))) :
    P.address (port (u.1.val.1,u.2))=(t,i) := by
  let v := (u.1.val.1,u.2)
  have hcell := congrArg (fun a : Cell k n × Fin (q*d) => a.1) eqn
  have hpin : (((ofFactorIntervals P direction port paired).tick v.1).2, (ofFactorIntervals P direction port paired).slot v)=(t.2,i) :=
    finProdFinEquiv.injective (congrArg (fun a : Cell k n × Fin (q*d) => a.2) eqn)
  have ht : P.tick (port (v.1,false))=t := Prod.ext hcell (congrArg (fun z : Fin q × Fin d => z.1) hpin)
  exact Prod.ext ((tick_side P port paired v).symm.trans ht) (congrArg (fun z : Fin q × Fin d => z.2) hpin)

private theorem literal_value (t : (Cell k n × Fin q)) (i : Fin d) :
    (ofFactorIntervals P direction port paired).literal (t.1,finProdFinEquiv (t.2,i))=P.literal t i := by
  change P.literal (t.1,(finProdFinEquiv.symm (finProdFinEquiv (t.2,i))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (t.2,i))).2=_
  rw [Equiv.symm_apply_apply]

theorem ofFactorIntervals_advice (j : Fin S) (outside : j ∉ Set.range port) :
    let t := P.tick j
    (ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,P.slot j)) = .inr (P.advice j) := by
  let t := P.tick j
  let i := P.slot j
  have unused : ∀ u, (ofFactorIntervals P direction port paired).dest u ≠ (t.1,finProdFinEquiv (t.2,i)) := by
    intro u eqn
    have hit := exact_source P direction port paired u eqn
    exact outside ⟨_,P.address.injective hit⟩
  exact (pinSource_unused (ofFactorIntervals P direction port paired).dest (ofFactorIntervals P direction port paired).literal _ unused).trans
    (congrArg Sum.inr ((literal_value P direction port paired t i).trans (P.literal_slot j)))

theorem ofFactorIntervals_header (t : (Cell k n × Fin q)) (i : Fin d) (hi : i.val < (P.header t).length) :
    (ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,i)) = .inr ((P.header t)[i.val]) := by
  have unused : ∀ u, (ofFactorIntervals P direction port paired).dest u ≠ (t.1,finProdFinEquiv (t.2,i)) := by
    intro u eqn
    let j := port (u.1.val.1,u.2)
    have hit := exact_source P direction port paired u eqn
    have h₁ : P.tick j=t := congrArg (fun a : (Cell k n × Fin q) × Fin d => a.1) hit
    have h₂ : (P.slot j).val=i.val := congrArg (fun a : (Cell k n × Fin q) × Fin d => a.2.val) hit
    rw [P.slot_val h₁] at h₂
    omega
  exact (pinSource_unused (ofFactorIntervals P direction port paired).dest (ofFactorIntervals P direction port paired).literal _ unused).trans
    (congrArg Sum.inr ((literal_value P direction port paired t i).trans (P.literal_header t i hi)))


/-- The unused end of the tick is padded with zeroes. -/
theorem ofFactorIntervals_padding (t : (Cell k n × Fin q)) (i : Fin d)
    (past : (P.header t).length+(P.inputBits t).length ≤ i.val) :
    (ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,i))=.inr false := by
  have unused : ∀ u, (ofFactorIntervals P direction port paired).dest u ≠ (t.1,finProdFinEquiv (t.2,i)) := by
    intro u eqn
    let j := port (u.1.val.1,u.2)
    have hit := exact_source P direction port paired u eqn
    have ht : P.tick j=t := congrArg (fun a : (Cell k n × Fin q) × Fin d => a.1) hit
    have hs : (P.slot j).val=i.val := congrArg (fun a : (Cell k n × Fin q) × Fin d => a.2.val) hit
    rw [P.slot_val ht] at hs
    have bound := List.idxOf_lt_length_of_mem (P.mem_inputBits.mpr ht)
    omega
  have off : ¬ i.val<(P.header t).length := by omega
  have past' : (P.inputBits t).length ≤ i.val-(P.header t).length := by omega
  rw [data,pinSource_unused (ofFactorIntervals P direction port paired).dest (ofFactorIntervals P direction port paired).literal _ unused,literal_value]
  simp [Layout.literal,off,List.getElem?_eq_none past']

/-- After substituting the labelled rail bits, each original input address has
the same value at the assigned pin. -/
theorem ofFactorIntervals_read (x : E × Bool → Bool) (j : Fin S) :
    let t := P.tick j
    ((ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,P.slot j))).elim
      (fun u => x (u.1.val.1,u.2)) id = (pinSource port P.advice j).elim x id := by
  dsimp only
  by_cases h : j ∈ Set.range port
  · obtain ⟨u,rfl⟩ := h
    rw [ofFactorIntervals_endpoint P direction port paired u,
      (pinSource_inl port P.advice (port u) u).mpr rfl]; rfl
  · rw [ofFactorIntervals_advice P direction port paired j h,
      pinSource_unused port P.advice j (fun u eqn => h ⟨u,eqn⟩)]; rfl

/-- A tick sees the original input in descriptor order immediately after the header. -/
theorem ofFactorIntervals_read_stream (x : E × Bool → Bool) (t : (Cell k n × Fin q))
    (i : Fin (P.inputBits t).length) :
    let pin : Fin d := ⟨(P.header t).length+i.val, by
      have := P.inputFits t
      have := i.isLt
      omega⟩
    ((ofFactorIntervals P direction port paired).data t.1 (finProdFinEquiv (t.2,pin))).elim (fun u => x (u.1.val.1,u.2)) id =
      (pinSource port P.advice ((P.inputBits t).get i)).elim x id := by
  let j := (P.inputBits t).get i
  obtain ⟨ht,hs⟩ := P.slot_get t i
  have read := ofFactorIntervals_read P direction port paired x j
  dsimp only at read ⊢
  change P.tick j=t at ht
  change (P.slot j).val=_ at hs
  have slotEq : P.slot j=⟨(P.header t).length+i.val,by
    have := P.inputFits t; have := i.isLt; omega⟩ := Fin.ext hs
  rw [ht,slotEq] at read
  exact read


end
end Hierarchy.GridThrough.PinAssignment

end OAI
