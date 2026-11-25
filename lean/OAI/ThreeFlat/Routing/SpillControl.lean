import OAI.ThreeFlat.Routing.SpillControlNetwork

namespace OAI
/-! # The complete deterministic selector for one sparse packing bank -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill
open Concentrator

universe u
variable {E R V : Type u} {F : Type*} [Fintype E] [LinearOrder E] [Fintype R] [LinearOrder R]
  [Fintype V] [DecidableEq V]

private theorem indicator_mul [CommSemiring F] (a b : Prop) [Decidable a] [Decidable b] :
    (if a then (1:F) else 0) * (if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha,hb]

private theorem control_product {I : Type*} [Fintype I] [CommSemiring F]
    (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (f : Fin 3 ⊕ I → F) (h₀ : f (.inl 0) = if a then 1 else 0)
    (h₁ : f (.inl 1) = if b then 1 else 0) (h₂ : f (.inl 2) = if c then 1 else 0)
    (hi : (∏ i, f (.inr i)) = if d then 1 else 0) :
    (∏ g, f g) = if a ∧ b ∧ c ∧ d then 1 else 0 := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_three,h₀,h₁,h₂,hi]
  simp only [indicator_mul,and_assoc]

private theorem checked_product {I : Type*} [Fintype I] [CommSemiring F]
    (p : I → Prop) [DecidablePred p] (f : I → F) (q : Prop) [Decidable q]
    (h : ∀ i, f i = if p i then 1 else 0) (ok : (∀ i, p i) ↔ q) :
    (∏ i, f i) = if q then 1 else 0 := by
  calc
    _ = ∏ i, (if p i then (1:F) else 0) := Finset.prod_congr rfl (fun i _ => h i)
    _ = if ∀ i, p i then 1 else 0 := by rw [Fintype.prod_ite_zero]; simp
    _ = _ := if_congr ok rfl rfl

private abbrev reportedMask {cap : ℕ} (b : TraceBits E V cap → Bool) : Finset E :=
  Finset.univ.filter (fun e => b (.inl e) = true)

section
variable [CommSemiring F] (N : E → Finset R) (G : ReserveGraph E V) (slots cap : ℕ)
  (A : Finset E) (P : Candidate N → Bool) (s : ReserveChoice E slots → Bool)
  (b : TraceBits E V cap → Bool)

private def gateValue (g : ControlGate E) : F :=
  TypedWiring.value (controlModules N G slots cap g) (fun k =>
    Sum.elim (controlPins N A P s) b (controlWire N slots cap g k))

omit [Fintype R] in
private theorem primaryValue : gateValue (F := F) N G slots cap A P s b (.inl 0) =
    if PrimaryValid N (fun e => decide (e ∈ A)) P then 1 else 0 :=
  greedyCheck_eval N _ P

omit [Fintype R] in
private theorem reserveValue : gateValue (F := F) N G slots cap A P s b (.inl 1) =
    if (fun t => b (.inr t)) = reserveTrace G slots cap (reportedMask b) then 1 else 0 := by
  have hh := reserveCheck_eval (F := F) G slots cap (reportedMask b) (fun t => b (.inr t))
  change TypedWiring.value (reserveCheck (F := F) G slots cap) b = _
  refine Eq.trans ?_ (hh.trans (if_congr Iff.rfl rfl rfl))
  apply congrArg (TypedWiring.value (reserveCheck (F := F) G slots cap))
  funext z
  cases z with
  | inl e => simp [reportedMask]
  | inr t => rfl

omit [Fintype R] in
private theorem selectValue : gateValue (F := F) N G slots cap A P s b (.inl 2) =
    if s = reservePick G b then 1 else 0 := by
  have sel : (fun k => Sum.elim (controlPins N A P s) b (controlWire N slots cap (.inl 2) k)) =
      Sum.elim b s := by funext k; cases k <;> rfl
  exact (congrArg (TypedWiring.value (reserveSelectNetwork (F := F) G slots cap)) sel).trans
    (reserveSelectNetwork_eval G slots cap b s)

private theorem auditValue (e : E) : gateValue (F := F) N G slots cap A P s b (.inr e) =
    if (e ∈ reportedMask b ↔ e ∈ missedPrimary A N P) ∧ b (finalRead cap e) = false then 1 else 0 := by
  rw [gateValue,controlModules,TypedWiring.localTable_value]
  have mask : (b (.inl e) = decide (decide (e ∈ A) = true ∧ ∀ r : N e, P ⟨e,r⟩ = false)) ↔
      (e ∈ reportedMask b ↔ e ∈ missedPrimary A N P) := by
    rw [Bool.eq_iff_iff]
    simp [reportedMask,missedPrimary]
  exact if_congr (and_congr mask Iff.rfl) rfl rfl

private theorem allAuditValue : (∏ e, gateValue (F := F) N G slots cap A P s b (.inr e)) =
    if reportedMask b = missedPrimary A N P ∧ ∀ e, b (finalRead cap e) = false then 1 else 0 := by
  let ok (e : E) := (e ∈ reportedMask b ↔ e ∈ missedPrimary A N P) ∧ b (finalRead cap e) = false
  have common : (∀ e, ok e) ↔ reportedMask b = missedPrimary A N P ∧ ∀ e, b (finalRead cap e) = false :=
    ⟨fun h => ⟨Finset.ext (fun e => (h e).1),fun e => (h e).2⟩,
     fun h e => ⟨Finset.ext_iff.mp h.1 e,h.2 e⟩⟩
  apply checked_product ok (fun e => gateValue N G slots cap A P s b (.inr e)) _ _ common
  intro e
  exact (auditValue (F := F) N G slots cap A P s b e).trans (if_congr Iff.rfl rfl rfl)

set_option maxHeartbeats 400000 in
private theorem moduleProduct :
    (∏ g, TypedWiring.value (controlModules (F := F) N G slots cap g) (fun k =>
      Sum.elim (controlPins N A P s) b (controlWire N slots cap g k))) =
      if PrimaryValid N (fun e => decide (e ∈ A)) P ∧
        (fun t => b (.inr t)) = reserveTrace G slots cap (reportedMask b) ∧
        s = reservePick G b ∧ reportedMask b = missedPrimary A N P ∧
        (∀ e, b (finalRead (V := V) cap e) = false) then 1 else 0 :=
  control_product _ _ _ _ (gateValue N G slots cap A P s b)
    (primaryValue N G slots cap A P s b) (reserveValue N G slots cap A P s b)
    (selectValue N G slots cap A P s b) (allAuditValue N G slots cap A P s b)

end

/-- A legal mask gives one primary decision and one reserve assignment; the
same network rejects whenever an unresolved active edge survives all rounds. -/
theorem controlNetwork_eval [CommSemiring F] (N : E → Finset R) (G : ReserveGraph E V)
    (slots cap : ℕ) (A : Finset E) (P : Candidate N → Bool) (s : ReserveChoice E slots → Bool) :
    let B := missedPrimary A N P
    TypedWiring.value (controlNetwork (F := F) N G slots cap) (controlPins N A P s) =
      if PrimaryValid N (fun e => decide (e ∈ A)) P ∧
        s = reservePick G (reserveReports G slots cap B) ∧ G.live slots B cap = ∅
      then 1 else 0 := by
  dsimp only
  let B := missedPrimary A N P
  let z := reserveReports G slots cap B
  rw [controlNetwork,TypedWiring.glue_value]
  simp_rw [moduleProduct]
  dsimp only [reportedMask]
  rw [Finset.sum_eq_single z]
  · have ha : (Finset.univ.filter fun e => z (.inl e) = true) = B := by ext; simp [z,reserveReports]
    have he (e : E) : z (finalRead cap e) = decide (e ∈ G.live slots B cap) := by
      by_cases h : cap = 0
      · simp [z,finalRead,reserveReports,h,ReserveGraph.live]
      · simp [z,finalRead,reserveReports,h,reserveTrace,Nat.sub_add_cancel (by omega : 1 ≤ cap)]
    have ht : (fun t => z (.inr t)) = reserveTrace G slots cap B := rfl
    have hfinal : (∀ e, z (finalRead cap e) = false) ↔ G.live slots B cap = ∅ := by
      simp only [he,decide_eq_false_iff_not,Finset.eq_empty_iff_forall_notMem]
    change (if PrimaryValid N (fun e => decide (e ∈ A)) P ∧
        (fun t => z (.inr t)) = reserveTrace G slots cap (Finset.univ.filter fun e => z (.inl e) = true) ∧
        s = reservePick G z ∧ (Finset.univ.filter fun e => z (.inl e) = true) = B ∧
        (∀ e, z (finalRead cap e) = false) then 1 else 0) = _
    simp only [ha,ht,hfinal,true_and]
    rfl
  · intro b _ hb
    apply ite_eq_right
    rintro ⟨_,tr,_,mask,_⟩
    apply hb
    funext t
    cases t with
    | inl e =>
      change b (.inl e) = decide (e ∈ B)
      have hh := Finset.ext_iff.mp mask e
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    | inr t =>
      change b (.inr t) = reserveTrace G slots cap B t
      exact (congrFun tr t).trans (congrArg (fun S => reserveTrace G slots cap S t) mask)
  · simp

end ThreeFlat.Routing.Spill

end
end OAI
