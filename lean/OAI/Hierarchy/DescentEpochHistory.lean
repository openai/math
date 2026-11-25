import OAI.Hierarchy.DescentOrderedReentryBasic
import OAI.Hierarchy.DescentInstalledEpoch
import OAI.Hierarchy.DescentWholeGrain

namespace OAI
/-! # Repeated physical subrounds and configured reset on every reachable history -/

namespace Hierarchy.DescentSixParty
open DescentResetInvoice Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

universe v
variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}



variable (G : PoweredGadget F) {u ε : ℝ} (hu : 0≤u) (he : 0≤ε) {h C Ht t : ℕ}

structure Epoch (H : Histories F d P bits) (G : PoweredGadget F)
    {u ε : ℝ} (hu : 0≤u) (he : 0≤ε) (t h C Ht : ℕ) where
  subrounds : Schedule G he (u:=u) t H
  grain : ℕ
  positive : 0<grain
  count : ∀c,((Schedule.finish G he subrounds).state c).graph.Edge→ℕ
  fit : ∀c e,((Schedule.finish G he subrounds).state c).graph.width e=count c e*grain
  reset : ∀c,ResetInput (((Schedule.finish G he subrounds).state c).granular
    (count c) grain (fit c)) u ε h C Ht
  terminals : ∀c,(reset c).Terminals
  order : ∀c,let W := (Schedule.finish G he subrounds).state c
             W.graph.Edge ↪ Fin (Fintype.card W.graph.Edge)
  tickets : ∀c,(reset c).placement.OrderedTickets
    (DescentOrderedReset.grains ((Schedule.finish G he subrounds).state c) (count c) (order c))
  reblock : ∀c,Normalize ((reset c).orderedReentry (terminals c)
    (DescentOrderedReset.grains ((Schedule.finish G he subrounds).state c) (count c) (order c)))

namespace Epoch
variable {H : Histories.{0, 0, v} F d P bits} (one : Epoch H G hu he t h C Ht)

/-- One field weight for each actual incoming profile history passes through the
reset unchanged. The returned state is its installed router with retained tables. -/
def finish : Histories.{0, 0, v} F d P bits :=
  let middle := Schedule.finish G he one.subrounds
  ⟨middle.Choice,middle.finite,fun c=>(one.reblock c).result,middle.weight⟩

theorem finish_value (x : Ports bits) : (one.finish G hu he).value x=H.value x := by
  refine Eq.trans ?_ (Schedule.finish_value G he H one.subrounds x)
  unfold Histories.value finish
  apply Finset.sum_congr rfl
  intro c _
  let mid := Schedule.finish G he one.subrounds
  let key := DescentOrderedReset.grains (mid.state c) (one.count c) (one.order c)
  exact congrArg (fun z => mid.weight c * z)
    (((one.reblock c).value x).trans (((one.reset c).orderedReentry_value (one.terminals c) key x).trans
      ((mid.state c).granular_value (one.count c) one.grain (one.fit c) x)))

theorem finish_bill (E X : ℝ) (epos : 0≤E) (xpos : 0≤X)
    (before : ∀c,u*(H.state c).tetherWidth≤E ∧ u*(H.state c).liveWidth≤X)
    (menu : reentryRate h C*(1-(2-G.rate)/4)^t≤1/2) (c : (one.finish G hu he).Choice) :
    u*((one.finish G hu he).state c).tetherWidth ≤ E ∧
    u*((one.finish G hu he).state c).liveWidth ≤ X/2+
      (258*reentryRate h C+reentryExteriorRate h C 256 Ht)*(E+ε) := by
  let mid := Schedule.finish G he one.subrounds
  have measured := Schedule.finish_bill G he H one.subrounds hu E X before c
  have mr := (one.reset c).bill hu he
  rw [MarkedWorld.granular_core,MarkedWorld.granular_tether] at mr
  have docked := (one.reset c).read_reentry (one.terminals c) hu he
  have nlive := docked.2.2
  rw [MarkedWorld.granular_core,MarkedWorld.granular_tether] at nlive
  have afterT := docked.2.1
  rw [MarkedWorld.granular_tether] at afterT
  have norm := (one.reblock c).bills
  refine ⟨?_,Schedule.reset_bill G he H one.subrounds hu E X epos xpos before c h C Ht menu ?_⟩
  · change u*(one.reblock c).result.tetherWidth≤E
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (norm.2.trans_eq afterT)) hu).trans measured.1
  · apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr norm.1) hu).trans
    change u * ((one.reset c).reenter (one.terminals c)).liveWidth ≤ _
    rw [nlive]
    push_cast
    have major : u*((one.reset c).world hu he).liveWidth+
        u*(mid.state c).liveWidth+u*(mid.state c).tetherWidth≤
        reentryRate h C*(u*(mid.state c).liveWidth+ε)+
          reentryExteriorRate h C 256 Ht*(u*(mid.state c).tetherWidth) := by
      dsimp only [mid] at *
      unfold reentryRate reentryExteriorRate
      nlinarith only [mr,he]
    have exterior : 0 ≤ reentryExteriorRate h C 256 Ht := by
      dsimp [reentryExteriorRate,splicedExteriorRate,exteriorRate,internalRate]
      positivity
    conv_lhs => simp only [mul_add]
    exact major.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left measured.1 exterior))

end Epoch

/-- Old history choices and newly returned states remain dependent and branch
specific. Only the number of subrounds and the finite rotor menu are fixed. -/
def Epochs : (J : ℕ) → Histories.{0, 0, v} F d P bits → Type (max 1 v)
  | 0,_ => PUnit
  | j+1,H => Σ one : Epoch H G hu he t h C Ht,Epochs j (one.finish G hu he)

namespace Epochs
def finish : {J : ℕ} → {H : Histories.{0, 0, v} F d P bits} →
    Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H → Histories.{0, 0, v} F d P bits
  | 0,H,_ => H
  | j+1,_H,plan => @finish j (plan.1.finish G hu he) plan.2

theorem value {J : ℕ} (H : Histories F d P bits)
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (x : Ports bits) :
    (finish G hu he run).value x=H.value x := by
  induction J generalizing H with
  | zero => rfl
  | succ j ih => exact (ih _ run.2).trans (run.1.finish_value G hu he x)

/-- Every different profile assignment at the final stage satisfies this
single geometric bound. The constant depends only on the fixed menus. -/
theorem core {J : ℕ} (H : Histories F d P bits)
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (E X : ℝ) (epos : 0≤E) (xpos : 0≤X)
    (before : ∀c,u*(H.state c).tetherWidth≤E ∧ u*(H.state c).liveWidth≤X)
    (menu : reentryRate h C*(1-(2-G.rate)/4)^t≤1/2) (c : (finish G hu he run).Choice) :
    let K := 258*reentryRate h C+reentryExteriorRate h C 256 Ht
    u*((finish G hu he run).state c).tetherWidth≤E ∧
      u*((finish G hu he run).state c).liveWidth ≤
        X/(2:ℝ)^J+2*(1-(1/2:ℝ)^J)*K*(E+ε) := by
  let K := 258*reentryRate h C+reentryExteriorRate h C 256 Ht
  have kpos : 0≤K := by dsimp [K,reentryRate,splicedRate,internalRate,reentryExteriorRate,splicedExteriorRate,exteriorRate];positivity
  induction J generalizing H X with
  | zero => simpa [finish] using before c
  | succ j ih =>
    let X' := X/2+K*(E+ε)
    have next := run.1.finish_bill G hu he E X epos xpos before menu
    have nonneg : 0≤X' := by dsimp [X'];positivity
    have rest := ih _ run.2 X' nonneg next c
    refine ⟨rest.1,rest.2.trans_eq ?_⟩
    change X'/(2:ℝ)^j+2*(1-(1/2:ℝ)^j)*K*(E+ε)=_
    simp only [X',pow_succ,div_pow,one_pow]
    ring

end Epochs
end
end Hierarchy.DescentSixParty

end OAI
