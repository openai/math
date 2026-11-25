import OAI.Hierarchy.DescentBitGadget
import OAI.Hierarchy.DescentMergedSiteLoad

namespace OAI
/-! # Local bit width before the selected six-party contraction -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {I P U F : Type} [Fintype I] [Field F] {d : ℕ} {w : P→ℕ}
variable (N : Network d P w) (pick : I×Fin 2↪N.Edge) (sw : I→Fin 8→ℕ)
local notation "M" => physical N pick sw

/-- A selected loop at an old site may contribute both of its arms. -/
theorem physical_old_siteLoad (u : N.Site) : siteLoad (M) (.inl u) ≤ 2*siteLoad N u := by
  classical
  let debit (e : N.Edge) := if N.src e=u ∨ N.dst e=u then N.width e else 0
  let bill : (M).Edge→ℕ := Sum.elim debit (Sum.elim (debit ∘ pick) (fun _=>0))
  have covered : siteLoad (M) (.inl u) ≤ ∑e,(bill e) := by
    unfold siteLoad
    apply Finset.sum_le_sum
    intro e _
    rcases e with e | (t | t)
    · cases h : selected N pick e with
      | none => simp [physical,source,target,width,bill,debit,h]
      | some t =>
        by_cases yes : N.src e=u <;> simp [physical,source,target,width,bill,debit,h,yes]
    · by_cases yes : N.dst (pick t)=u <;> simp [physical,source,target,width,bill,debit,yes]
    · simp [physical,source,target,bill]
  have sub : (∑t,debit (pick t)) ≤ ∑e,debit e := by
    calc
      _ = ∑e ∈ Finset.univ.map pick,debit e := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  calc
    _ ≤ _ := covered
    _ = (∑e,debit e)+(∑t,debit (pick t)) := by
      change (∑ e : GadgetNetwork.Edge (I:=I) N, bill e) = _
      simp [bill, Fintype.sum_sum_type]
    _ ≤ _ := by change _ ≤ 2*(∑e,debit e);omega

/-- Every genuine incident cable at a motif site is one of its fixed role ports. -/
def roleCable (i : I) (j : Fin 6) : RolePort j→Incident (M) (.inr (i,j))
  | .inl (.inl ⟨s,h⟩) => ⟨.inl (pick (i,s)),Or.inr (by simp [physical,target,h])⟩
  | .inl (.inr ⟨s,h⟩) => ⟨.inr (.inl (i,s)),Or.inl (by simp [physical,source,h])⟩
  | .inr (.inl ⟨s,h⟩) => ⟨.inr (.inr (i,s)),Or.inl (by simp [physical,source,h])⟩
  | .inr (.inr ⟨s,h⟩) => ⟨.inr (.inr (i,s)),Or.inr (by simp [physical,target,h])⟩

theorem nativeRole_cable (i : I) (j : Fin 6) (s : RolePort j) :
    nativeRole N pick sw i j s=.inl (roleCable N pick sw i j s) := by
  rcases s with (s|s)|(s|s) <;> rfl

theorem roleCable_surjective (i : I) (j : Fin 6) :
    Function.Surjective (roleCable N pick sw i j) := by
  rintro ⟨e,hit⟩
  rcases e with e | (⟨k,s⟩ | ⟨k,s⟩)
  · cases h : selected N pick e with
    | none => simp [physical,source,target,h] at hit
    | some t =>
      obtain ⟨k,s⟩ := t
      have hh : k=i ∧ demandSrc s=j := by simpa [physical,source,target,h] using hit
      obtain ⟨rfl,hj⟩ := hh
      refine ⟨.inl (.inl ⟨s,hj⟩),Subtype.ext ?_⟩
      exact congrArg Sum.inl (selected_spec N pick h)
  · have hh : k=i ∧ demandDst s=j := by simpa [physical,source,target] using hit
    obtain ⟨rfl,hj⟩ := hh
    exact ⟨.inl (.inr ⟨s,hj⟩),rfl⟩
  · have hh : (k=i ∧ supplySrc s=j) ∨ (k=i ∧ supplyDst s=j) := by
      simpa [physical,source,target] using hit
    rcases hh with ⟨rfl,hj⟩ | ⟨rfl,hj⟩
    · exact ⟨.inr (.inl ⟨s,hj⟩),rfl⟩
    · exact ⟨.inr (.inr ⟨s,hj⟩),rfl⟩

theorem physical_role_arity (j : Fin 6) : Fintype.card (RolePort j) ≤ 8 := by decide +revert

variable (G : PoweredGadget F) (z : I→ℕ) (p : I→Profile G.C)
variable (fit : ∀i s,N.width (pick (i,s))=z i*G.b)
local notation "S" => branchWidth G z p
local notation "R" => physical N pick S

include fit in
theorem roleCable_width (i : I) (j : Fin 6) (s : RolePort j) :
    (R).width (roleCable N pick S i j s).val ≤ z i*(G.C+G.k+G.b+2) := by
  rcases s with (⟨s,hs⟩|⟨s,hs⟩)|(⟨s,hs⟩|⟨s,hs⟩)
  · change N.width (pick (i,s)) ≤ _
    rw [fit]
    exact Nat.mul_le_mul_left _ (by omega)
  · change N.width (pick (i,s)) ≤ _
    rw [fit]
    exact Nat.mul_le_mul_left _ (by omega)
  all_goals
    change z i*(((p i).1 s).val+G.k) ≤ _
    apply Nat.mul_le_mul_left
    have bound := ((p i).1 s).isLt
    omega

private theorem incident_sum (u : N.Site) :
    siteLoad N u=∑e : Incident N u,N.width e.val := by
  classical
  rw [←Finset.sum_subtype (Finset.univ.filter (fun e=>N.src e=u ∨ N.dst e=u)) (by simp) N.width,
    Finset.sum_filter]
  rfl

include fit in
theorem physical_role_siteLoad (i : I) (j : Fin 6) :
    siteLoad (R) (.inr (i,j)) ≤ 8*(z i*(G.C+G.k+G.b+2)) := by
  classical
  refine (incident_sum (R) (.inr (i,j))).le.trans ?_
  calc
    _ ≤ ∑e : Incident (R) (.inr (i,j)),z i*(G.C+G.k+G.b+2) := by
      apply Finset.sum_le_sum
      intro e _
      obtain ⟨s,rfl⟩ := roleCable_surjective N pick S i j e
      exact roleCable_width N pick G z p fit i j s
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ ((Fintype.card_le_of_surjective _ (roleCable_surjective N pick S i j)).trans
        (physical_role_arity j))

variable (W : World F d P w) (chosen : I×Fin 2↪W.graph.Edge)
variable {Z : ℕ} (room : ∀i,z i≤Z) (old : SiteBits (U:=U) W.graph)
local notation "R'" => physical W.graph chosen S
local notation "B'" => physicalBits G W chosen z room p old

theorem physical_old_hidden (u : W.graph.Site) : (B' (.inl u)).hiddenWidth=(old u).hiddenWidth := rfl
theorem physical_old_nodeBits (u : W.graph.Site) (n : (old u).Node) :
    (B' (.inl u)).nodeBits n=(old u).nodeBits n := rfl

theorem physical_role_count (i : I) (j : Fin 6) : Fintype.card (B' (.inr (i,j))).Node=1 := by
  change Fintype.card Unit=1
  exact Fintype.card_unique

theorem physical_role_hidden (i : I) (j : Fin 6) : (B' (.inr (i,j))).Hidden=Empty := rfl

theorem physical_old_hidden_sum (u : W.graph.Site) :
    (∑h : (B' (.inl u)).Hidden,(B' (.inl u)).hiddenWidth h)=∑h : (old u).Hidden,(old u).hiddenWidth h := rfl

theorem physical_role_hidden_sum (i : I) (j : Fin 6) :
    (∑h : (B' (.inr (i,j))).Hidden,(B' (.inr (i,j))).hiddenWidth h)=0 := by
  change (∑h : Empty,(Empty.elim h : ℕ))=0
  simp

theorem physical_role_nodeBits (fit' : ∀i s,W.graph.width (chosen (i,s))=z i*G.b)
    (i : I) (j : Fin 6) (n : (B' (.inr (i,j))).Node) :
    (B' (.inr (i,j))).nodeBits n ≤ 8*(z i*(G.C+G.k+G.b+2)) := by
  classical
  change (∑a : Fin (Fintype.card (RolePort j)),boundaryWidth (R') _
    (nativeRole W.graph chosen S i j ((roleIndex j).symm a))) ≤ _
  calc
    _ ≤ ∑_a : Fin (Fintype.card (RolePort j)),z i*(G.C+G.k+G.b+2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [nativeRole_cable]
      exact roleCable_width W.graph chosen G z p fit' i j _
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (physical_role_arity j)

theorem physical_role_volume (fit' : ∀i s,W.graph.width (chosen (i,s))=z i*G.b)
    (i : I) (j : Fin 6) (n : (B' (.inr (i,j))).Node) :
    siteLoad (R') (.inr (i,j))+(B' (.inr (i,j))).nodeBits n ≤ 20*(G.C+G.k+G.b+2)*z i := by
  have a := physical_role_siteLoad W.graph chosen G z p fit' i j
  have b := physical_role_nodeBits G z p W chosen room old fit' i j n
  calc
    _ ≤ 8*(z i*(G.C+G.k+G.b+2))+8*(z i*(G.C+G.k+G.b+2)) := Nat.add_le_add a b
    _ ≤ 20*(z i*(G.C+G.k+G.b+2)) := by omega
    _ = _ := by ring

end
end Hierarchy.DescentKernelHistory

end OAI
