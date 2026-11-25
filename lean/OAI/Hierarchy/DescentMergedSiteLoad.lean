import OAI.Hierarchy.DescentMergedCableCost

namespace OAI
/-! # Incident width at a genuine merged site of a six-party subround -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {D d : ℕ} {P : Type*} {bits : P → ℕ} {I C : Type} [Fintype I]
variable (N : Network D P bits)

/-- An incident cable supplies one local table argument, including when it is a loop. -/
def siteLoad (u : N.Site) : ℕ := ∑ e, if N.src e = u ∨ N.dst e = u then N.width e else 0

def touches {A : Type} (atSite : N.Site → A) (v : A) (e : N.Edge) : Prop :=
  atSite (N.src e) = v ∨ atSite (N.dst e) = v

def oldBill {A : Type} (atSite : N.Site → A) (v : A) (e : N.Edge) : ℕ :=
  if touches N atSite v e then N.width e else 0

/-- Charge each touching cable to one of its original incident sites in the fiber. -/
theorem oldBill_le {A : Type} (atSite : N.Site → A) (v : A) :
    (∑ e : N.Edge, oldBill N atSite v e) ≤ ∑ u : {u : N.Site // atSite u = v}, siteLoad N u.val := by
  let debit (e : N.Edge) (u : {u : N.Site // atSite u = v}) :=
    if N.src e = u.val ∨ N.dst e = u.val then N.width e else 0
  calc
    _ ≤ ∑ e : N.Edge, ∑ u, debit e u := by
      apply Finset.sum_le_sum
      intro e _
      by_cases h : touches N atSite v e
      · rw [oldBill, ite_eq_left h]
        have found : ∃ u : {u : N.Site // atSite u = v}, N.src e = u.val ∨ N.dst e = u.val := by
          rcases h with hs | ht
          · exact ⟨⟨N.src e, hs⟩, Or.inl rfl⟩
          · exact ⟨⟨N.dst e, ht⟩, Or.inr rfl⟩
        obtain ⟨u, hu⟩ := found
        have one := Finset.single_le_sum (s := Finset.univ) (f := debit e)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
        simpa only [debit, ite_eq_left hu] using one
      · simp [oldBill, h]
    _ = _ := Finset.sum_comm

variable (pick : I × Fin 2 ↪ N.Edge) (sw : I → Fin 8 → ℕ) (layout : Bool) (pack : N.Site → C)
variable (pos : Merged N pick layout pack → EuclideanSpace ℝ (Fin d)) (hpos : ∀ c, ‖pos c‖ ≤ 1)
local notation "loc" => newSite N pick layout pack
local notation "oldLoc" => (fun u : N.Site => loc (Sum.inl u))
local notation "M" => physical N pick sw
local notation "Q" => merged N pick sw layout pack pos hpos
variable (v : Merged N pick layout pack)

private def activeAt (i : I) : Prop := ∃ s : Fin 2, touches N oldLoc v (pick (i,s))

omit [Fintype I] in
/-- Each of the three clusters contains at least one actual demand endpoint. -/
private theorem party_active (i : I) (j : Fin 6) (hj : loc (.inr (i,j)) = v) :
    activeAt N pick layout pack v i := by
  have cover (l : Bool) (k : Fin 6) :
      (∃ s, cluster l (demandSrc s) = cluster l k) ∨ ∃ s, cluster l (demandDst s) = cluster l k := by
    decide +revert
  rcases cover layout j with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact ⟨s, Or.inl ((source_merge N pick layout pack i s).trans
      ((Quot.sound (Join.privateWire i _ _ hs)).trans hj))⟩
  · exact ⟨s, Or.inr ((target_merge N pick layout pack i s).trans
      ((Quot.sound (Join.privateWire i _ _ hs)).trans hj))⟩

private def siteCharge : Edge (I:=I) N → ℕ
  | .inl e => oldBill N oldLoc v e
  | .inr (.inl _) => 0
  | .inr (.inr t) => if activeAt N pick layout pack v t.1 then sw t.1 t.2 else 0

private theorem incident_le_charge (e : (M).Edge) (crosses : loc ((M).src e) ≠ loc ((M).dst e)) :
    (if loc ((M).src e) = v ∨ loc ((M).dst e) = v then (M).width e else 0) ≤
      siteCharge N pick sw layout pack v e := by
  rcases e with e | (⟨i,s⟩ | ⟨i,k⟩)
  · cases sel : selected N pick e with
    | none =>
      simp only [siteCharge, oldBill, touches, physical, source, target, sel, width]
      exact le_of_eq (@ite_cond_congr ℕ _ (touches N oldLoc v e) _
        (Classical.propDecidable (touches N oldLoc v e)) (N.width e) 0 rfl)
    | some t =>
      obtain ⟨i,s⟩ := t
      have picked := selected_spec N pick sel
      subst e
      exact (crosses (by
        simpa only [physical, source, target, selected_pick] using
          (source_merge N pick layout pack i s))).elim
  · exact (crosses (target_merge N pick layout pack i s).symm).elim
  · change (if loc (.inr (i,supplySrc k)) = v ∨ loc (.inr (i,supplyDst k)) = v then sw i k else 0) ≤
      (if activeAt N pick layout pack v i then sw i k else 0)
    split
    next h =>
      have a := h.elim (party_active N pick layout pack v i (supplySrc k))
        (party_active N pick layout pack v i (supplyDst k))
      simp [a]
    next => exact Nat.zero_le _

/-- An instance whose parties touch this site can charge its supply to a selected old cable in
its fiber. The injection selecting physical demands prevents duplicate charges across instances. -/
theorem merged_site_load_le (a : ℕ) (budget : ∀ i s, (∑ k, sw i k) ≤ a*N.width (pick (i,s))) :
    siteLoad Q v ≤ (a+1)*(∑ u : {u : N.Site // oldLoc u = v}, siteLoad N u.val) := by
  classical
  let bill := oldBill N oldLoc v
  let total := ∑ e : N.Edge, bill e
  let paid := ∑ t : I × Fin 2, bill (pick t)
  let extra := ∑ i, ∑ k, if activeAt N pick layout pack v i then sw i k else 0
  have pay_le : paid ≤ total := by
    have subset := Finset.sum_le_sum_of_subset_of_nonneg (f := bill)
      (Finset.subset_univ (Finset.univ.map pick)) (fun _ _ _ => Nat.zero_le _)
    simpa only [Finset.sum_map, Function.comp_apply, paid, total] using subset
  have extra_le : extra ≤ a * paid := by
    dsimp only [extra, paid]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : activeAt N pick layout pack v i
    · simp only [ite_eq_left h]
      obtain ⟨s, hs⟩ := h
      have one := Finset.single_le_sum (s := Finset.univ) (f := fun t : Fin 2 => bill (pick (i,t)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
      have hit : bill (pick (i,s)) = N.width (pick (i,s)) := ite_eq_left hs
      rw [hit] at one
      exact (budget i s).trans (Nat.mul_le_mul_left a one)
    · simp [h]
  calc
    siteLoad Q v ≤ ∑ e : (M).Edge, siteCharge N pick sw layout pack v e := by
      refine le_trans ?_ (crossing_sum_le N pick sw layout pack pos hpos (siteCharge N pick sw layout pack v))
      unfold siteLoad
      apply Finset.sum_le_sum
      intro e _
      exact incident_le_charge N pick sw layout pack v e.val e.property
    _ = total + extra := by
      change (∑ e : Edge (I:=I) N, siteCharge N pick sw layout pack v e) = _
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, siteCharge, total, bill, extra,
        Finset.sum_const_zero, zero_add]
    _ ≤ (a+1)*total := by
      have H := extra_le.trans (Nat.mul_le_mul_left a pay_le)
      rw [Nat.add_mul, one_mul]
      omega
    _ ≤ _ := Nat.mul_le_mul_left _ (oldBill_le N oldLoc v)

/-- The strict gadget inequality gives the same constant for every profile and either layout. -/
theorem merged_site_load_five {F : Type*} [Field F] (G : PoweredGadget F) (z : I → ℕ)
    (p : I → Profile G.C) (fit : ∀ i s, N.width (pick (i,s)) = z i*G.b) :
    let w := fun i e => z i*(((p i).1 e).val+G.k)
    siteLoad (merged N pick w layout pack pos hpos) v ≤
      5 * (∑ u : {u : N.Site // oldLoc u = v}, siteLoad N u.val) := by
  dsimp only
  apply merged_site_load_le N pick _ layout pack pos hpos v 4
  intro i s
  calc
    _ ≤ z i*(G.C+8+8*G.k) := by
      simpa only [Finset.mul_sum] using Nat.mul_le_mul_left (z i) (profile_cost G.k (p i))
    _ ≤ z i*(4*G.b) := Nat.mul_le_mul_left _ G.paid.le
    _ = _ := by rw [fit]; ring

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
