import OAI.Hierarchy.ProtocolRAMCalendarInventory
import OAI.Hierarchy.ProtocolRAMCalendarArchive
import OAI.Hierarchy.ProbeRepairAccount

namespace OAI
/-! # Measured purchase and saturation along the full native reserve calendar -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
variable {w q d : ℕ} {I : Type*} [Fintype I]

/-- The accurate and saturated bought branches both replay actual inner states.
The saturation predicate is the native mode word at each genuine attempt. -/
def AccountColumns.purchase (A : AccountColumns I) (C : Chart w q d) (mem : Memory w)
    (p h n K cap : ℕ) (ρ γ ρBuy reward s : ℝ) : Prop :=
  let x := A.trial C mem p h
  let y := A.trial C mem p (h+1)
  (∃ r : A.bank.ReplayRows n A.payloadWidth K cap ρ γ ρBuy reward s x y,
    r.m = C.mesh.reserveSteps ∧ (∀ k<r.m, r.attempts k=C.mesh.innerFuel) ∧
    ∀ k<r.m, ∀ b≤r.attempts k, r.states k b = A.inner C mem p h k b) ∨
  (∃ r : A.bank.SaturatedReplayRows n A.payloadWidth K cap ρ γ ρBuy reward s x y,
    r.m = C.mesh.reserveSteps ∧ (∀ k<r.m, r.attempts k=C.mesh.innerFuel) ∧
    (∀ k<r.m, ∀ b≤r.attempts k, r.states k b = A.inner C mem p h k b) ∧
    ∀ k<r.m, ∀ b<r.attempts k, r.active k b = decide (observedInnerMode C mem p h k b=2))

theorem AccountColumns.purchase_readback (A : AccountColumns I) (C : Chart w q d) (mem : Memory w)
    {p h n K cap : ℕ} {ρ γ ρBuy reward s : ℝ} (buy : A.purchase C mem p h n K cap ρ γ ρBuy reward s) :
    A.bank.PurchaseReadback n A.payloadWidth K cap ρ γ ρBuy reward s (A.trial C mem p h) (A.trial C mem p (h+1)) := by
  rcases buy with ⟨r,_⟩ | ⟨r,_⟩
  · exact Or.inl ⟨r⟩
  · exact Or.inr ⟨r⟩

/-- The controller stores one zero-or-one flag per actual candidate at purchase. -/
def purchaseCount (C : Chart w q d) (mem : Memory w) (p h : ℕ) : ℕ :=
  let a := Attempt.outer p h
  let out := after C (.attempt a) (trialState C mem p h)
  (Finset.univ.filter (fun j : Fin (C.layout a).candidates=>out ((repair C a).purchaseOut+j.val)≠0)).card

theorem inner_advance (c : Mesh) (H : Attempt→ℕ) (p h steps j : ℕ) (early : j<steps)
    (fuel : 0<c.innerFuel) (buy : H (.outer p h)=3)
    (openSlot : ¬reserveCap c H p h steps) (law : innerLaw c H p h j) :
    ∃ b<c.innerFuel, H (.inner p h j b)=1 ∧ ∀ k<c.innerFuel, b<k → H (.inner p h j k)=0 := by
  have pass : ∃ b<c.innerFuel,H (.inner p h j b)=1 := by
    by_contra none
    let k := c.innerFuel-1
    have bound : k<c.innerFuel := by dsimp [k]; omega
    have on : ¬disabled c H (.inner p h j k) := by
      rintro (notBuy | cap | ⟨i,hi,hit⟩)
      · exact notBuy buy
      · rcases cap with z | ⟨t,ht,ht'⟩
        · exact openSlot (Or.inl z)
        · exact openSlot (Or.inr ⟨t,ht.trans early,ht'⟩)
      · exact none ⟨i,hi.trans bound,hit⟩
    have modes := law k bound
    rw [ite_eq_right on] at modes
    exact openSlot (Or.inr ⟨j,early,modes.resolve_left (fun hit=>none ⟨k,bound,hit⟩)⟩)
  obtain ⟨b,hb,pass⟩ := pass
  refine ⟨b,hb,pass,fun k hk lt=>?_⟩
  have off : disabled c H (.inner p h j k) := Or.inr (Or.inr ⟨b,lt,pass⟩)
  simpa only [ite_eq_left off] using law k hk

/-- All inner transitions here are individual native reads on this purchase.
The activation inequality is due only on an actual low discrepancy word.
The same capped integer stock and physical postings are used in both cases. -/
structure Acquisition (A : AccountColumns I) (C : Chart w q d) (mem : Memory w) (p h n K cap : ℕ)
    (ρ γ ρBuy reward s : ℝ) where
  fee : ℝ
  feeBound : ℝ
  dimension : ℝ
  boxMax : ℝ
  mesh_pos : 0<C.mesh.reserveSteps
  mesh_fits : C.mesh.reserveSteps≤A.payloadWidth
  dimension_bound : (Fintype.card I:ℝ)≤dimension*n
  cap_pos : 0≤boxMax
  cap_bound : ∀ i,A.box i≤boxMax
  entry_fits : ∀ i,(A.trial C mem p h).bits i≤cap*A.payloadWidth
  fee_bound : purchaseCount C mem p h*fee≤n*feeBound
  fuel_budget : feeBound+dimension*cap*boxMax+ρBuy*reward/8≤C.mesh.innerFuel*(ρ*γ/(8*K))
  initial_cash : (A.inner C mem p h 0 0).paid≤(A.trial C mem p h).paid+purchaseCount C mem p h*fee
  initial_stock : ∀ i,(A.inner C mem p h 0 0).bits i=(A.trial C mem p h).bits i/2
  terminal : A.inner C mem p h C.mesh.reserveSteps 0=A.trial C mem p (h+1)
  repaired : ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel, observedInnerMode C mem p h j b=2 →
    Nonempty (A.bank.FailedRows n A.payloadWidth K cap ρ γ (replayTime s C.mesh.reserveSteps j)
      (A.inner C mem p h j b) (A.inner C mem p h j (b+1)))
  skipped : ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel, observedInnerMode C mem p h j b≠2 →
    A.inner C mem p h j (b+1)=A.inner C mem p h j b
  retained : ∀ j<C.mesh.reserveSteps, ∀ i,(A.inner C mem p h (j+1) 0).bits i =
    min (A.bank.replayFeed C.mesh.reserveSteps j (A.trial C mem p h) (A.inner C mem p h j C.mesh.innerFuel) i)
      (cap*A.payloadWidth)
  charged : ∀ j<C.mesh.reserveSteps, (A.inner C mem p h (j+1) 0).paid≤(A.inner C mem p h j C.mesh.innerFuel).paid+
    pairing (bitStock A.payloadWidth (spillBits cap A.payloadWidth (A.bank.replayFeed C.mesh.reserveSteps j
      (A.trial C mem p h) (A.inner C mem p h j C.mesh.innerFuel)))) A.box
  activation : ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel, observedInnerMode C mem p h j b=1 →
    2*((purchaseCount C mem p h:ℝ)*fee+(n:ℝ)*ρBuy*reward/4) ≤
      s*divergence A.a A.M A.coefficient
        (maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem p h)))
        (maximizer A.a A.M (replayTime s C.mesh.reserveSteps j) A.coefficient A.box
          (A.bank.units A.payloadWidth (A.inner C mem p h j b)))
  mesh_error : (C.mesh.reserveSteps:ℝ)*(Fintype.card I*(2*boxMax/A.payloadWidth+
      (((cap:ℝ)+2+cap)/C.mesh.reserveSteps)^2/(2*s*A.a))) ≤ (n:ℝ)*ρBuy*reward/8

theorem Acquisition.purchase {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {p h n K cap : ℕ} {ρ γ ρBuy reward s : ℝ}
    (Q : Acquisition A C mem p h n K cap ρ γ ρBuy reward s)
    {total : ℕ} (archive : ArchiveRoom C mem total) (hp : p<total) (hh : h<C.mesh.outerFuel)
    (buy : observedMode C mem p h=3) : A.purchase C mem p h n K cap ρ γ ρBuy reward s := by
  classical
  let H := observedHistory C mem
  have laws (j : ℕ) (hj : j<C.mesh.reserveSteps) : innerLaw C.mesh H p h j := archive.inner_law p h j hp hh hj
  let X := A.trial C mem p h
  let Y := A.trial C mem p (h+1)
  let states := A.inner C mem p h
  by_cases exhausted : reserveCap C.mesh H p h C.mesh.reserveSteps
  · obtain ⟨j,hj,paid⟩ := innerSaturated_paid C.mesh H p h _ archive.innerFuel laws exhausted
    let actual (k b : ℕ) := decide (observedInnerMode C mem p h k b=2)
    have full : C.mesh.innerFuel≤((Finset.range C.mesh.innerFuel).filter fun b=>actual j b).card := by
      have same : (Finset.range C.mesh.innerFuel).filter (fun b=>actual j b)=Finset.range C.mesh.innerFuel := by
        apply Finset.filter_eq_self.mpr
        intro b hb
        exact decide_eq_true (paid b (Finset.mem_range.mp hb))
      simp [same]
    let R : A.bank.SaturatedReplayRows n A.payloadWidth K cap ρ γ ρBuy reward s X Y :=
      { m:=C.mesh.reserveSteps, mesh_pos:=Q.mesh_pos, states:=states, attempts:=fun _=>C.mesh.innerFuel,
        active:=actual, sliceId:=j, fuel:=C.mesh.innerFuel, selected:=hj, full:=full,
        bought:=purchaseCount C mem p h, fee:=Q.fee, feeBound:=Q.feeBound, dimension:=Q.dimension,boxMax:=Q.boxMax,
        dimension_bound:=Q.dimension_bound,cap_pos:=Q.cap_pos,cap_bound:=Q.cap_bound,entry_fits:=Q.entry_fits,
        fee_bound:=Q.fee_bound,fuel_budget:=Q.fuel_budget,initial_cash:=Q.initial_cash,initial_stock:=Q.initial_stock,
        terminal:=Q.terminal,repaired:=fun k hk u hu yes=>Q.repaired k hk u hu (of_decide_eq_true yes),
        skipped:=fun k hk u hu no=>by
          have eq := Q.skipped k hk u hu (of_decide_eq_false no)
          exact ⟨congrArg Inventory.paid eq,congrArg Inventory.bits eq⟩,
        retained:=Q.retained,charged:=Q.charged }
    exact Or.inr ⟨R,rfl,fun _ _=>rfl,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl⟩
  · have active (j : ℕ) (hj : j<C.mesh.reserveSteps) :=
      inner_advance C.mesh H p h C.mesh.reserveSteps j hj archive.innerFuel buy exhausted (laws j hj)
    let R : A.bank.ReplayRows n A.payloadWidth K cap ρ γ ρBuy reward s X Y :=
      { m:=C.mesh.reserveSteps,mesh_pos:=Q.mesh_pos,mesh_fits:=Q.mesh_fits,states:=states,
        attempts:=fun _=>C.mesh.innerFuel,bought:=purchaseCount C mem p h,fee:=Q.fee,boxMax:=Q.boxMax,
        box_bound:=Q.cap_bound,entry_fits:=Q.entry_fits,initial_cash:=Q.initial_cash,initial_stock:=Q.initial_stock,
        terminal:=Q.terminal,repairs:=fun j hj u hu=>by
          by_cases yes : observedInnerMode C mem p h j u=2
          · exact Or.inl (Q.repaired j hj u hu yes)
          · have eq := Q.skipped j hj u hu yes
            exact Or.inr ⟨congrArg Inventory.paid eq,congrArg Inventory.bits eq⟩,
        retained:=Q.retained,charged:=Q.charged,mesh_error:=Q.mesh_error,
        activation:=fun j hj=>by
          obtain ⟨i,hi,hit,later⟩ := active j hj
          have stable (v : ℕ) (beginAt : i≤v) (endAt : v≤C.mesh.innerFuel) : states j v=states j i := by
            induction v with
            | zero => have := Nat.eq_zero_of_le_zero beginAt; subst i; rfl
            | succ v ih =>
              by_cases eqn : i=v+1
              · rw [eqn]
              · have iv : i≤v := by omega
                have hv : v<C.mesh.innerFuel := by omega
                have skip : observedInnerMode C mem p h j v≠2 := by
                  by_cases same : i=v
                  · subst v; change observedInnerMode C mem p h j i=1 at hit; omega
                  · have off := later v hv (by omega)
                    change observedInnerMode C mem p h j v=0 at off
                    omega
                exact (Q.skipped j hj v hv skip).trans (ih iv hv.le)
          change _≤_*divergence _ _ _ _ (maximizer _ _ _ _ _ (A.bank.units A.payloadWidth (states j C.mesh.innerFuel)))
          rw [stable _ hi.le le_rfl]
          exact Q.activation j hj i hi hit }
    exact Or.inl ⟨R,rfl,fun _ _=>rfl,fun _ _ _ _=>rfl⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
