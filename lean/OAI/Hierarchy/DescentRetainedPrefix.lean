import OAI.Hierarchy.DescentAtomAllowance

namespace OAI
/-! # Paying a fixed price for all history records in each chronological prefix -/

namespace Hierarchy.DescentCompiler
open scoped BigOperators Classical

/-- A branch only pays for the initial records and the true births at each subsequent step.
Sites may be renamed, merged, or split between steps. -/
theorem retained_prefix (total born : ℕ→ℕ) (n : ℕ) (initial : total 0=born 0)
    (advance : ∀i<n,total (i+1)=total i+born (i+1)) :
    total n=∑i∈Finset.range (n+1),born i := by
  induction n with
  | zero => simpa using initial
  | succ n ih =>
    rw [advance n (Nat.lt_succ_self n),ih (fun i hi=>advance i (Nat.lt_succ_of_lt hi)),Finset.sum_range_succ (n:=n+1)]

/-- The allowance for all scheduled births implies the same bound for every occupied
prefix, including a prefix that has no selected pairs or installed gates. -/
theorem retained_atom_slack {t J c fixed slope R r m n : ℕ} (hJ : 0<J) (within : n≤(t+1)*J)
    (H : ℕ→ℕ) (oldHost : H 0≤m) (growth : ∀i,H (i+1)≤H i*(2^c*r))
    (S : ℕ→Type) [∀i,Fintype (S i)] (slots : ∀i≤(t+1)*J,Fintype.card (S i)≤H i*blocks R r ((t+1)*J) i)
    (births : ∀i,S i→ℕ) (limit : ∀i≤(t+1)*J,∀s,births i s≤2^(fixed+slope*J))
    (total : ℕ→ℕ) (initial : total 0=∑s,births 0 s)
    (advance : ∀i<n,total (i+1)=total i+∑s,births (i+1) s) :
    total n*2^J≤(m*(R*r^((t+1)*J)))*(2^J)^atomExponent t c fixed slope := by
  let tags (i : ℕ) (s : S i) := List.replicate (births i s) ()
  have bound := atom_lists (t:=t) (J:=J) (c:=c) (fixed:=fixed) (slope:=slope) (R:=R) (r:=r) (m:=m)
    hJ H oldHost growth S slots tags (by intro i hi s;simpa [tags] using limit i hi s)
  simp only [tags,List.length_replicate] at bound
  rw [retained_prefix total (fun i=>∑s,births i s) n initial advance]
  have sub := Finset.range_mono (Nat.succ_le_succ within)
  exact (Nat.mul_le_mul_right _ (Finset.sum_le_sum_of_subset (f:=fun i=>∑s,births i s) sub)).trans bound

/-- Normalize the integer prefix allowance at the common, fixed history price. -/
theorem retained_real {T power mass total : ℕ} (hT : 0<T) (h : total*T≤mass*T^power) :
    (1/(T:ℝ)^power)*(total:ℝ)≤(mass:ℝ)/T := by
  have t : (0:ℝ)<T := by exact_mod_cast hT
  have tp : (0:ℝ)<(T:ℝ)^power := pow_pos t _
  have hh : (total:ℝ)*T≤(mass:ℝ)*T^power := by exact_mod_cast h
  rw [one_div_mul_eq_div]
  exact (div_le_div_iff₀ tp t).mpr hh

end Hierarchy.DescentCompiler

end OAI
