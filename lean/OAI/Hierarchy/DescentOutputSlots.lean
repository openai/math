import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI
/-! # Disjoint physical output rows for the common contact reservations -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {C : Type*} [Fintype C] {Y : ℕ}

def rowCount (Y : ℕ) (scale cap : ℝ) := ⌈cap*Y/(8*scale)⌉₊

theorem output_room (cap : C → ℝ) {S : ℝ} (positive : 0<S) (nonneg : ∀c,0≤cap c)
    (budget : ∑c,cap c≤2*S) (contacts : 4*Fintype.card C≤Y) :
    (∑c,rowCount Y S (cap c))≤Y := by
  have ceilBound (c : C) : (rowCount Y S (cap c):ℝ) ≤cap c*Y/(8*S)+1 :=
    (Nat.ceil_lt_add_one (by exact div_nonneg (mul_nonneg (nonneg c) (by positivity)) (by positivity))).le
  have summed := Finset.sum_le_sum (s:=Finset.univ) fun c _ => ceilBound c
  rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul] at summed
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at summed
  have used : (∑c,cap c)*Y/(8*S)≤Y/4 := by
    apply (div_le_iff₀ (by positivity : 0<8*S)).2
    linarith [mul_le_mul_of_nonneg_right budget (show 0≤(Y:ℝ) by positivity)]
  have count : 4*(Fintype.card C:ℝ)≤Y := by exact_mod_cast contacts
  exact_mod_cast (show (∑c,(rowCount Y S (cap c):ℝ))≤Y by linarith)

private def before (c : C) := Finset.univ.filter fun z => Fintype.equivFin C z < Fintype.equivFin C c

def firstSlot (n : C → ℕ) (c : C) := ∑ z∈before c,n z

private theorem span (n : C → ℕ) (c : C) :
    firstSlot n c+n c=∑ z∈insert c (before c),n z := by
  classical
  rw [Finset.sum_insert (by simp [before])]
  exact Nat.add_comm ..

theorem slot_fit (n : C → ℕ) (c : C) : firstSlot n c+n c≤∑z,n z := by
  rw [span]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _

theorem slot_before (n : C → ℕ) {c d : C} (lt : Fintype.equivFin C c < Fintype.equivFin C d) :
    firstSlot n c+n c≤firstSlot n d := by
  classical
  rw [span]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro z member
  rcases Finset.mem_insert.mp member with rfl | h
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp h).2 lt⟩

/-- A contiguous named interval for every contact; on opposite sides of the
direct link the same local ordinal labels the two reserved endpoints. -/
def outputSlot (n : C → ℕ) (fit : ∑c,n c≤Y) (p : Σ c,Fin (n c)) : Fin Y :=
  ⟨firstSlot n p.1+p.2.val,by have := p.2.isLt;have := (slot_fit n p.1).trans fit;omega⟩

theorem outputSlot_injective (n : C → ℕ) (fit : ∑c,n c≤Y) : Function.Injective (outputSlot n fit) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ same
  have equal := congrArg Fin.val same
  change firstSlot n c+i.val=firstSlot n d+j.val at equal
  rcases lt_trichotomy (Fintype.equivFin C c) (Fintype.equivFin C d) with h | h | h
  · have b := slot_before n h
    have := i.isLt
    omega
  · have : c=d := (Fintype.equivFin C).injective h
    subst d
    apply congrArg (Sigma.mk c)
    exact Fin.ext (by omega)
  · have b := slot_before n h
    have := j.isLt
    omega

variable [NeZero Y]

private theorem rowCount_pos {S cap u : ℝ} {N : ℕ} (sPos : 0<S) (uPos : 0<u)
    (traffic : (N:ℝ)*u≤cap) (i : Fin N) : 0<rowCount Y S cap := by
  have hn : 0<(N:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hc := (mul_pos hn uPos).trans_le traffic
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hc hy) (mul_pos (by norm_num) sPos))

/-- Round robin within a contact: its endpoint on each adjacent base obtains
the same ordinal, even when their first reserved physical rows differ. -/
def chooseOutput (cap : C → ℝ) (N : C → ℕ) {S u : ℝ} (sPos : 0<S) (uPos : 0<u)
    (traffic : ∀c,(N c:ℝ)*u≤cap c) (p : Σ c,Fin (N c)) : Σ c,Fin (rowCount Y S (cap c)) :=
  ⟨p.1,⟨p.2.val%rowCount Y S (cap p.1),Nat.mod_lt _ (rowCount_pos sPos uPos (traffic p.1) p.2)⟩⟩

/-- The physical endpoints at the two neighboring bases can have different
absolute addresses, while the direct link uses exactly the same local ordinal.
The same bundle serial is supplied by the actual contact at both ends. -/
theorem paired_output_rows {H : Type*} [Fintype H] (left : C → ℝ) (right : H → ℝ)
    (NL : C → ℕ) (NR : H → ℕ) {S u : ℝ} (sPos : 0<S) (uPos : 0<u)
    (lCap : ∀c,(NL c:ℝ)*u≤left c) (rCap : ∀c,(NR c:ℝ)*u≤right c)
    (lFit : (∑c,rowCount Y S (left c))≤Y) (rFit : (∑c,rowCount Y S (right c))≤Y)
    (c : C) (t : H) (common : left c=right t) (amount : NL c=NR t) (b : Fin (NL c)) :
    let l := outputSlot _ lFit (chooseOutput left NL sPos uPos lCap ⟨c,b⟩)
    let r := outputSlot _ rFit (chooseOutput right NR sPos uPos rCap ⟨t,b.cast amount⟩)
    l.val-firstSlot (fun i=>rowCount Y S (left i)) c =
      r.val-firstSlot (fun i=>rowCount Y S (right i)) t := by
  simp [outputSlot,chooseOutput,common]

omit [Fintype C] in
private theorem quotient_bound (cap : C → ℝ) (N : C → ℕ) {S u : ℝ}
    (sPos : 0<S) (uPos : 0<u) (traffic : ∀c,(N c:ℝ)*u≤cap c) (c : C) :
    N c/rowCount Y S (cap c)≤⌊8*S/((Y:ℝ)*u)⌋₊ := by
  let q := rowCount Y S (cap c)
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  by_cases empty : q=0
  · change N c/q≤_
    simp [empty]
  have hq : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero empty
  have lower : cap c*(Y:ℝ)≤(q:ℝ)*(8*S) := (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
  have counts : ((N c/q:ℕ):ℝ)*q≤N c := by exact_mod_cast Nat.div_mul_le_self (N c) q
  apply Nat.le_floor
  apply (le_div_iff₀ (mul_pos hy uPos)).2
  apply le_of_mul_le_mul_left (a:=(q:ℝ)) _ hq
  calc
    _ = (((N c/q:ℕ):ℝ)*q)*u*Y := by ring
    _ ≤ (N c:ℝ)*u*Y := by gcongr
    _ ≤ cap c*Y := mul_le_mul_of_nonneg_right (traffic c) hy.le
    _ ≤ _ := lower

/-- At a physical output row, two bundles with the same round-robin quotient
are equal: the disjoint intervals recover the contact and residue, and
division with remainder recovers the bundle's original ordinal. -/
theorem output_rows (cap : C → ℝ) (N : C → ℕ) {S u : ℝ} (sPos : 0<S) (uPos : 0<u)
    (traffic : ∀c,(N c:ℝ)*u≤cap c)
    (fit : ∑c,rowCount Y S (cap c)≤Y) (j : Fin Y) :
    let dest := fun p : Σ c,Fin (N c) => outputSlot _ fit (chooseOutput cap N sPos uPos traffic p)
    ((Finset.univ.filter (fun p => dest p=j)).card:ℝ)*u≤8*S/Y+u := by
  classical
  dsimp only
  let n := fun c=>rowCount Y S (cap c)
  let dest := fun p : Σ c,Fin (N c) => outputSlot _ fit (chooseOutput cap N sPos uPos traffic p)
  let fiber := Finset.univ.filter (fun p => dest p=j)
  let bound := ⌊8*S/((Y:ℝ)*u)⌋₊
  let ticket (p : fiber) : Fin (bound+1) :=
    ⟨p.val.2.val/n p.val.1, by
      have := quotient_bound (Y:=Y) cap N sPos uPos traffic p.val.1
      exact Nat.lt_succ_of_le ((Nat.div_le_div_right p.val.2.isLt.le).trans this)⟩
  have inject : Function.Injective ticket := by
    rintro ⟨⟨c,a⟩,ha⟩ ⟨⟨d,b⟩,hb⟩ eq
    have q := congrArg Fin.val eq
    change a.val/n c=b.val/n d at q
    have same := ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2.symm)
    have out := outputSlot_injective n fit same
    have cd := congrArg Sigma.fst out
    change c=d at cd
    subst d
    have r := congrArg (fun p : Σ c,Fin (n c) => p.2.val) out
    change a.val%n c=b.val%n c at r
    have eqAB : a=b := Fin.ext (by
      have p := Nat.mod_add_div a.val (n c)
      have t := Nat.mod_add_div b.val (n c)
      rw [r,q] at p
      exact p.symm.trans t)
    subst b
    rfl
  have count : fiber.card≤bound+1 := by simpa using Fintype.card_le_of_injective ticket inject
  have creal : (fiber.card:ℝ)≤(bound:ℝ)+1 := by exact_mod_cast count
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  have bf : (bound:ℝ)≤8*S/((Y:ℝ)*u) := Nat.floor_le (by positivity)
  change (fiber.card:ℝ)*u≤_
  have pay := (le_div_iff₀ (mul_pos hy uPos)).mp bf
  have priced := mul_le_mul_of_nonneg_right creal (mul_pos uPos hy).le
  have aux : (fiber.card:ℝ)*u≤(8*S+u*Y)/Y := by
    apply (le_div_iff₀ hy).2
    linarith only [pay,priced]
  apply aux.trans_eq
  field_simp

end
end Hierarchy.DescentBaseProfile

end OAI
