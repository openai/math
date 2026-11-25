import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI
/-! # Whole-group packing and occupied batches for the tagged calls -/

namespace Hierarchy.TaggedShorterPacking

open Finset

def load {ι : Type*} (size : ι→ℕ) (xs : List ι) := (xs.map size).sum

private theorem load_append {ι : Type*} (size : ι→ℕ) (xs ys : List ι) :
    load size (xs++ys)=load size xs+load size ys := by simp [load]

/-- Right-to-left next fit. Each original group is kept intact. -/
def pack {ι : Type*} (size : ι→ℕ) (H : ℕ) : List ι→List (List ι)
  | [] => []
  | x::xs =>
    match pack size H xs with
    | [] => [[x]]
    | g::gs =>
      if size x+load size g≤H then (x::g)::gs else [x]::g::gs

/-- The output preserves the order of groups, all loads fit, and all bins
except the leading partially filled bin are more than half full. -/
theorem pack_spec {ι : Type*} (size : ι→ℕ) (H : ℕ) (xs : List ι)
    (fits : ∀ x∈xs,2*size x≤H) :
    (pack size H xs).flatten=xs ∧
    (∀ g∈pack size H xs,load size g≤H) ∧
    (∀ g∈(pack size H xs).tail,H<2*load size g) := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    have hx := fits x (by simp)
    obtain ⟨flat,upper,filled⟩ := ih (fun z hz=>fits z (List.mem_cons_of_mem _ hz))
    cases eq : pack size H xs with
    | nil =>
      rw [eq] at flat
      simp only [List.flatten_nil] at flat
      subst xs
      simp [pack,load]
      omega
    | cons g gs =>
      rw [eq] at flat upper filled
      simp only [List.flatten_cons] at flat
      simp only [List.tail_cons] at filled
      by_cases h : size x+load size g≤H
      · simp only [pack,eq,ite_eq_left h,List.flatten_cons,List.cons_append,List.tail_cons]
        refine ⟨congrArg (x::·) flat,?_,filled⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl|hmem
        · simpa only [load,List.map_cons,List.sum_cons] using h
        · exact upper _ (List.mem_cons_of_mem _ hmem)
      · simp only [pack,eq,ite_eq_right h,List.flatten_cons,List.cons_append,List.nil_append,List.tail_cons]
        refine ⟨congrArg (x::·) flat,?_,?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl|hmem
          · simp [load]; omega
          · exact upper _ hmem
        · intro z hz
          rcases List.mem_cons.mp hz with rfl|hmem
          · omega
          · exact filled _ hmem

private theorem full_count {ι : Type*} (size : ι→ℕ) (H : ℕ) (gs : List (List ι))
    (full : ∀ g∈gs,H≤2*load size g) :
    gs.length*H ≤ 2*load size gs.flatten := by
  induction gs with
  | nil => simp [load]
  | cons g gs ih =>
    have h := full g (by simp)
    have k := ih (fun b hb=>full b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons,List.flatten_cons,load_append,Nat.add_mul,one_mul]
    omega

/-- The number of supergroups is at most twice the site volume divided by
capacity, with room for one incomplete bin. -/
theorem pack_count {ι : Type*} (size : ι→ℕ) (H : ℕ) (xs : List ι)
    (fits : ∀ x∈xs,2*size x≤H) :
    (pack size H xs).length*H ≤ 2*load size xs+H := by
  obtain ⟨flat,_,full⟩ := pack_spec size H xs fits
  cases eq : pack size H xs with
  | nil => simp
  | cons g gs =>
    rw [eq] at flat full
    have k := full_count size H gs (fun b hb=>(full b hb).le)
    rw [←flat,List.flatten_cons,load_append]
    simp only [List.length_cons,Nat.add_mul,one_mul]
    omega

/-- Number of nonempty B-transport batches, with no charge for an empty
supergroup. -/
def batches (a B : ℕ) := (a+B-1)/B

theorem batch_bounds (a : ℕ) {B : ℕ} (hb : 0<B) :
    a≤batches a B*B ∧ batches a B*B≤a+B := by
  have r := Nat.mod_lt (a+B-1) hb
  have eq := Nat.mod_add_div (a+B-1) B
  rw [Nat.mul_comm B] at eq
  unfold batches
  omega

/-- The quotient and remainder assign every transport a distinct position in
one of the batches installed for its supergroup. -/
def batchEmbedding (a B : ℕ) (hb : 0<B) : Fin a ↪ Fin (batches a B) × Fin B where
  toFun i := (⟨i.val/B,(Nat.div_lt_iff_lt_mul hb).mpr
    (i.isLt.trans_le (batch_bounds a hb).1)⟩,⟨i.val%B,Nat.mod_lt _ hb⟩)
  inj' i j same := by
    have hq := congrArg (fun z : Fin (batches a B) × Fin B => z.1.val) same
    have hr := congrArg (fun z : Fin (batches a B) × Fin B => z.2.val) same
    change i.val/B=j.val/B at hq
    change i.val%B=j.val%B at hr
    apply Fin.ext
    calc i.val = i.val%B+B*(i.val/B) := (Nat.mod_add_div _ _).symm
         _ = j.val := by rw [hq,hr,Nat.mod_add_div]

/-- Rounding separately in each supergroup costs at most one batch there. -/
theorem batches_sum {ι : Type*} (groups : Finset ι) (a : ι→ℕ) {B : ℕ} (hb : 0<B) :
    (∑ i∈groups,batches (a i) B)*B ≤ (∑ i∈groups,a i)+groups.card*B := by
  rw [Finset.sum_mul]
  have h := Finset.sum_le_sum (s := groups) (fun i _=>(batch_bounds (a i) hb).2)
  simpa [Finset.sum_add_distrib,nsmul_eq_mul] using h

/-- A K=2B list reserves twice the batch capacity. At most half the physical
modules are ever occupied. -/
theorem half_modules {ι : Type*} (groups : Finset ι) (a : ι→ℕ) {B : ℕ} (hb : 0<B)
    {c n : ℝ} (active : ((∑ i∈groups,a i : ℕ):ℝ)≤c*n)
    (padding : (groups.card:ℝ)*(2*B:ℕ)≤c*n) :
    2*(∑ i∈groups,batches (a i) B) ≤ ⌈6*c*n/(2*B:ℕ)⌉₊ := by
  have est := batches_sum groups a hb
  have est' : ((∑ i∈groups,batches (a i) B : ℕ):ℝ)*(B:ℝ)≤
      ((∑ i∈groups,a i : ℕ):ℝ)+(groups.card:ℝ)*B := by exact_mod_cast est
  have hb' : 0<(B:ℝ) := by exact_mod_cast hb
  have z : ((2*B:ℕ):ℝ)=2*(B:ℝ) := by norm_num
  rw [z] at padding
  have m := Nat.le_ceil (6*c*n/((2*B:ℕ):ℝ))
  rw [z] at m
  have h : 2*((∑ i∈groups,batches (a i) B:ℕ):ℝ) ≤ 6*c*n/(2*(B:ℝ)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  exact_mod_cast h.trans m

/-- Hardwiring the full menu of candidate batches costs only a constant
multiple of the available physical modules. The multiple uses a uniform lower
bound on c, so it works simultaneously over all widths. -/
theorem candidate_modules (g H B sites n : ℕ) (hb : 0<B) (hBH : B≤H) (hHn : H≤n)
    {C c c₀ : ℝ} (hC : 0≤C) (hc₀ : 0<c₀) (hc : c₀≤c)
    (count : g*H≤2*sites+H) (volume : (sites:ℝ)≤C*n) :
    ((g*batches H B : ℕ):ℝ) ≤ (4*C+2)/(3*c₀)*⌈6*c*n/(2*(B:ℝ))⌉₊ := by
  let M := ⌈6*c*n/(2*(B:ℝ))⌉₊
  have hb' : 0<(B:ℝ) := Nat.cast_pos.mpr hb
  have batches' : (batches H B:ℝ)*B≤2*H := by
    exact_mod_cast (show batches H B*B ≤ 2*H by have := (batch_bounds H hb).2; omega)
  have groups : (g:ℝ)*H≤2*(sites:ℝ)+H := by exact_mod_cast count
  have Hn : (H:ℝ)≤n := by exact_mod_cast hHn
  have total : (g:ℝ)*(batches H B:ℝ)*B≤(4*C+2)*n := by
    nlinarith [mul_le_mul_of_nonneg_left batches' (Nat.cast_nonneg g)]
  have lower : 6*c*n≤(M:ℝ)*(2*(B:ℝ)) :=
    (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
  have scale : 3*c₀*n≤(M:ℝ)*B := by nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)]
  change _ ≤ (4*C+2)/(3*c₀)*(M:ℝ)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  push_cast
  apply le_of_mul_le_mul_right (a := (B:ℝ)) _ hb'
  nlinarith [mul_le_mul_of_nonneg_left total (show 0≤3*c₀ by positivity),
    mul_le_mul_of_nonneg_left scale (show 0≤4*C+2 by positivity)]

/-- Once the linear site bound C and a uniform lower fraction c are known,
choose a fixed dyadic K/H. The residual rounding then costs at most cn. -/
theorem choose_fraction {C c : ℝ} (hC : 0≤C) (hc : 0<c) :
    ∃ d : ℕ, ∀ (groups H K sites n : ℕ),
      groups*H ≤ 2*sites+H → (sites:ℝ)≤C*n → H≤n →
      (K:ℝ)≤H*(1/2:ℝ)^d → (groups:ℝ)*K ≤ c*n := by
  obtain ⟨d,hd⟩ := exists_pow_lt_of_lt_one (show 0<c/(2*C+1) by positivity)
    (show (1/2:ℝ)<1 by norm_num)
  refine ⟨d,?_⟩
  intro groups H K sites n count size hn scale
  have big : (groups:ℝ)*H≤2*(sites:ℝ)+H := by exact_mod_cast count
  have Hn : (H:ℝ)≤n := by exact_mod_cast hn
  have count' : (groups:ℝ)*H≤(2*C+1)*n := by linarith
  have bound := (lt_div_iff₀ (show 0<2*C+1 by positivity)).mp hd
  calc
    _ ≤ (groups:ℝ)*(H*(1/2:ℝ)^d) := mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg _)
    _ ≤ ((2*C+1)*n)*(1/2:ℝ)^d := by
      rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right count' (by positivity)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right bound.le (Nat.cast_nonneg n)]

/-- Multiplying a dyadic supergroup capacity by the chosen fraction subtracts
exactly d from its address length. -/
theorem shorter_address (d h : ℕ) (large : d≤h) :
    (2:ℝ)^(h-d)=(2:ℝ)^h*(1/2:ℝ)^d := by
  have inv : (2:ℝ)^d*(1/2:ℝ)^d=1 := by rw [←mul_pow]; norm_num
  calc
    (2:ℝ)^(h-d) = 2^(h-d)*(2^d*(1/2:ℝ)^d) := by rw [inv,mul_one]
    _ = ((2:ℝ)^(h-d)*2^d)*(1/2:ℝ)^d := by ring
    _ = (2:ℝ)^h*(1/2:ℝ)^d := by rw [←pow_add,Nat.sub_add_cancel large]

/-- When the supergroup capacity is dyadic, all sufficiently large address
lengths admit an even batch size at precisely the fixed dyadic fraction. -/
theorem dyadic_batch (d h : ℕ) (large : d<h) :
    ∃ B : ℕ, 0<B ∧ (2*B:ℝ)=((2:ℕ)^h:ℕ)*(1/2:ℝ)^d := by
  obtain ⟨k,eq⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt large)
  refine ⟨2^k,by positivity,?_⟩
  rw [eq]
  push_cast
  rw [pow_add,pow_succ]
  have inv : (2:ℝ)^d*(1/2:ℝ)^d=1 := by rw [←mul_pow]; norm_num
  calc 2*(2:ℝ)^k = ((2:ℝ)^d*(1/2:ℝ)^d)*(2*2^k) := by rw [inv]; ring
       _ = _ := by ring

end Hierarchy.TaggedShorterPacking

end OAI
