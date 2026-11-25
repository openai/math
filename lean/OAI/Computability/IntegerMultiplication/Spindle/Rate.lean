import OAI.Computability.IntegerMultiplication.Code.Decompose

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Code Finset
noncomputable def acres (τ : ℝ) (D : ℕ) (l : List Tally) :=
  (l.map fun i => ((D:ℝ)^τ)^i.length).sum
variable {τ : ℝ} {D : ℕ}
def height (v : Tally × List Tally) := 2^v.1.length
private theorem exactRate (r : ℕ→ℝ) (l : List Tally) (m : ℕ) (h : ∀ x∈l,x.length < m) :
    (l.map (fun x => r x.length)).sum =
      (range m).sum (fun x => (l.count (tally x) : ℝ)*r x) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons,List.sum_cons,ih (fun _ h' => h _ (List.mem_cons_of_mem _ h'))]
    have a := h _ List.mem_cons_self
    have e (x) : ((i::l).count (tally x) : ℝ) =
        (if i.length=x then 1 else 0)+(l.count (tally x) : ℝ) := by
      by_cases g : i.length=x
      · have u : i=tally x := by rw [← g,recover_tally]
        simp [u]; ring
      have u : i≠tally x := by intro e; rw [e,tally_length] at g; contradiction
      simp [u,g]
    simp_rw [e,add_mul,sum_add_distrib,ite_mul]
    simp [a]

theorem brave (t : 0<τ) (d : 2≤D) :
    ∃ M : ℕ, ∀ l : List Tally, (∀ i,l.count i ≤ D) →
      acres τ D l+1 ≤ (M:ℝ)*((volume D l+1:ℕ):ℝ)^τ := by
  let z : ℝ := (D:ℝ)^τ
  have hf : 1<z := Real.one_lt_rpow (by exact_mod_cast d) t
  have z0 : 0<z := by linarith
  obtain ⟨M,u⟩ := exists_nat_gt ((D:ℝ)*z/(z-1) + 1)
  refine ⟨M,fun l g => ?_⟩
  have geom (m) : (∑ i∈range m,z^i)*(z-1)=z^m-1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  let m := l.toFinset.sup List.length
  have he : acres τ D l ≤ D * (∑ i∈range (m+1), z^i):= by
    change (List.map (fun x : List Unit => z^x.length) l).sum ≤ _
    rw [exactRate (fun i => z^i) l (m+1) (by
      intro x e; exact Nat.lt_succ_of_le (Finset.le_sup (f:=List.length) (by simpa using e))),Finset.mul_sum]
    gcongr with i _
    exact_mod_cast g (tally i)
  have u0 : z^m ≤ ((volume D l+1:ℕ):ℝ)^τ := by
    have dg : D^m≤volume D l + 1 := by
      by_cases h : l.toFinset.Nonempty
      · obtain ⟨i,a,e⟩ : ∃ i ∈ l.toFinset,List.length i=m := by
          obtain ⟨i,e,r⟩ := exists_max_image l.toFinset List.length h
          exact ⟨i,e,le_antisymm (Finset.le_sup (f:=List.length) e) (Finset.sup_le r) |>.symm.symm⟩
        rw [← e]
        unfold volume
        have h := List.single_le_sum (l:=l.map (fun x => D^x.length)) (fun _ _ => Nat.zero_le _) _
          (List.mem_map_of_mem (a:=i) (by simpa using a))
        omega
      have e : l=[] := by
        cases l with
        | nil => rfl
        | cons x l => exfalso; exact h ⟨x,by simp⟩
      subst l; simp [m]
    have ht : z^m = ((D^m:ℕ):ℝ)^τ := by
      unfold z
      push_cast
      rw [← Real.rpow_natCast_mul (by positivity),← Real.rpow_mul_natCast (by positivity),mul_comm]
      -- x^(n:ℝ)^... ?
    rw [ht]; gcongr
  have top : acres τ D l ≤ ((D:ℝ)*z/(z-1))*((volume D l+1:ℕ):ℝ)^τ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (show 0<z-1 by linarith)]
    calc
     _ ≤ ((D:ℝ) * ∑ i∈range (m+1), z^i) * (z-1) := by gcongr
     _ = (D:ℝ)*(z^m*z - 1) := by rw [mul_assoc,geom,pow_succ]
     _ ≤ (D:ℝ)*(z^m*z) := by gcongr; linarith
     _ ≤ (D:ℝ)*(((volume D l+1:ℕ):ℝ)^τ*z) := by gcongr
     _ = _ := by ring
  have v : 1 ≤ ((volume D l+1:ℕ):ℝ)^τ := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 (volume D l)) t.le
  have c := mul_lt_mul_of_pos_right u (show (0:ℝ)<((volume D l+1:ℕ):ℝ)^τ by linarith)
  linarith
end Spindle

end IntegerMultiplication
end Computability
end OAI
