import OAI.ThreeFlat.Diagonal.RefreshDemandChoice

namespace OAI
/-! # Word bounds for native scoring and canonical tile selection -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open RAM RAM.PhysicalPinsExpr RAM.MotifRows MotifIntegerChoice
open scoped Classical BigOperators
noncomputable section

variable {E : Type} [Fintype E] {n W k : ℕ}
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

private theorem totals_fit (l : List (Formula n)) (h : ∀ f ∈ l, Fit f) : Fit (totals l) := by
  induction l with
  | nil => trivial
  | cons f l ih => exact ⟨h _ (by simp),ih (fun g hg => h _ (by simp [hg])),trivial⟩

private theorem biggest_fit (l : List (Formula n)) {cap : ℕ} (hc : cap<2^W)
    (h : ∀ f ∈ l, Fit f ∧ V f ≤ cap) : Fit (biggest l) := by
  induction l with
  | nil => trivial
  | cons f l ih =>
    obtain ⟨hf,hv⟩ := h f (by simp)
    have tail g (hg : g ∈ l) := h g (by simp [hg])
    have ht := ih tail
    have htv : V (biggest l) ≤ cap := (biggest_le ..).mpr (fun g hg => (tail g hg).2)
    refine ⟨hf,ht,hv.trans_lt hc,htv.trans_lt hc,?_⟩
    split <;> assumption

private theorem scoreFields_fit (b : E → Formula n) (d : E → ℕ)
    (fb : ∀ e, Fit (b e)) (hs : sentinel (fun e => V (b e)) < 2^W)
    (hd : ∀ e, sentinel (fun e => V (b e)) + d e < 2^W) :
    Fit (scoreFields b d) ∧ V (scoreFields b d) ≤ sentinel (fun e => V (b e)) := by
  let coords := (Finset.univ : Finset E).toList
  let cap := sentinel (fun e => V (b e))
  let bad := plus (.lit 1) (totals (coords.map b))
  have fbadv : V bad = cap := by
    change 1+V (totals _) = 1+_
    simp only [totals_value,List.map_map,coords,Finset.sum_map_toList,Function.comp_apply]
  have fbad : Fit bad := by
    refine ⟨trivial,totals_fit data mem vs _ ?_,trivial⟩
    intro f hf
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hf
    exact fb e
  have hv (e : E) : V (b e) < cap := by
    have := Finset.single_le_sum (f := fun j => V (b j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    dsimp only [cap,sentinel]
    omega
  have bounded (e : E) :
      Fit (required bad (b e) (d e)) ∧ V (required bad (b e) (d e)) ≤ cap := by
    have p := hd e
    change cap+d e < _ at p
    by_cases z : d e = 0
    · simp only [required,z,ite_true]
      constructor
      · refine ⟨fb e,trivial,(hv e).trans hs,by positivity,?_⟩
        split
        · trivial
        · exact fbad
      · change (if _ then 0 else V bad) ≤ cap
        split
        · exact Nat.zero_le _
        · exact fbadv.le
    · constructor
      · simp only [required,z,ite_false]
        refine ⟨⟨fb e,trivial,trivial⟩,trivial,?_,?_⟩
        · change V (b e) + (d e-1) < 2^W
          have := hv e
          omega
        · change d e < 2^W
          omega
      · rw [required_value,fbadv]
        exact ((need_le_iff (hv e)).mpr (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero z))).trans (hv e).le
  have bounds f (hf : f ∈ coords.map fun e => required bad (b e) (d e)) :
      Fit f ∧ V f ≤ cap := by
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hf
    exact bounded e
  exact ⟨biggest_fit data mem vs _ hs bounds,(biggest_le ..).mpr fun f hf => (bounds f hf).2⟩

/-- Numeric copy and choice expressions fit every word width accommodating
the demand sentinel plus the largest fixed tile coordinate. -/
theorem chooseFields_fits (b : E → Formula n) (d : Fin (k+1) → E → ℕ)
    (fb : ∀ e, Fit (b e)) (hs : sentinel (fun e => V (b e)) < 2^W)
    (hd : ∀ j e, sentinel (fun e => V (b e)) + d j e < 2^W) :
    Fit (chooseFields b d).1 ∧ Fit (chooseFields b d).2 := by
  let cap := sentinel (fun e => V (b e))
  let good := fun (z : Formula n × Formula n) => Fit z.1 ∧ Fit z.2 ∧ V z.1 ≤ cap
  let row (j : Fin (k+1)) : Formula n × Formula n := (scoreFields b (d j), Formula.lit j.val)
  have hr j : good (row j) := by
    obtain ⟨h,s⟩ := scoreFields_fit data mem vs b (d j) fb hs (hd j)
    exact ⟨h,trivial,s⟩
  have better_good (p q : Formula n × Formula n) (hp : good p) (hq : good q) : good (better p q) := by
    obtain ⟨fp,sp,bp⟩ := hp
    obtain ⟨fq,sq,bq⟩ := hq
    by_cases less : V q.1 < V p.1 <;>
      simp [good,better,Formula.Fits,Formula.natural,natTest,less,fp,sp,fq,sq,bp,bq,bp.trans_lt hs,bq.trans_lt hs]
  have fold_good (p : Formula n × Formula n) (l : List (Formula n × Formula n)) (hp : good p)
      (hl : ∀ j ∈ l, good j) : good (l.foldl better p) := by
    induction l generalizing p with
    | nil => exact hp
    | cons j l ih =>
      exact ih (better p j) (better_good p j hp (hl _ (by simp))) (fun i hi => hl _ (by simp [hi]))
  have h : good (chooseFields b d) := by
    apply fold_good (row 0) _ (hr _)
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact hr i.succ
  exact ⟨h.1,h.2.1⟩

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
