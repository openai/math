import OAI.Optimization.LinearProgramming.Lattice.LLLSwapNative
import Mathlib.Data.Nat.Size

/-! Integer arithmetic and coefficient-table accesses in the executable native LLL swap. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- One execution, counting integer additions, subtractions, multiplications and divisions,
and reads and writes of individual entries of the stored coefficient matrix. -/
structure SwapMeter (α : Type) where
  value : α
  arithmetic : ℕ
  reads : ℕ
  writes : ℕ
  /-- Results of all arithmetic instructions in evaluation order. -/
  registers : List ℤ := []

private instance : Monad SwapMeter where
  pure x := ⟨x,0,0,0,[]⟩
  bind x f :=
    let y := f x.value
    ⟨y.value, x.arithmetic+y.arithmetic, x.reads+y.reads, x.writes+y.writes,x.registers++y.registers⟩

private def scalar (x : ℤ) : SwapMeter ℤ := ⟨x,1,0,0,[x]⟩

private def pivotArithmetic (prev next : ℕ) (B : ℤ) (d : ℕ) : SwapMeter ℕ := do
  let p ← scalar ((next : ℤ) * prev)
  let b ← scalar (B * B)
  let q ← scalar (p + b)
  let h ← scalar (q / d)
  pure h.toNat

private def tailArithmetic (prev next : ℕ) (B : ℤ) (d : ℕ) (a b : ℤ) :
    SwapMeter (ℤ × ℤ) := do
  let p ← scalar ((prev : ℤ)*a)
  let q ← scalar (B*b)
  let t ← scalar (p+q)
  let x ← scalar (t/d)
  let p' ← scalar ((next : ℤ)*b)
  let q' ← scalar (B*a)
  let t' ← scalar (p'-q')
  let y ← scalar (t'/d)
  pure (x,y)

private theorem pivotArithmetic_eq (prev next : ℕ) (B : ℤ) (d : ℕ) :
    pivotArithmetic prev next B d =
    ⟨(((next : ℤ)*prev+B^2)/d).toNat,4,0,0,
      [(next : ℤ)*prev,B^2,(next : ℤ)*prev+B^2,((next : ℤ)*prev+B^2)/d]⟩ := by rw [pow_two]; rfl

private theorem tailArithmetic_eq (prev next : ℕ) (B : ℤ) (d : ℕ) (a b : ℤ) :
    tailArithmetic prev next B d a b =
    ⟨(((prev : ℤ)*a+B*b)/d,((next : ℤ)*b-B*a)/d),8,0,0,
      [(prev : ℤ)*a,B*b,(prev : ℤ)*a+B*b,((prev : ℤ)*a+B*b)/d,
        (next : ℤ)*b,B*a,(next : ℤ)*b-B*a,((next : ℤ)*b-B*a)/d]⟩ := rfl

private theorem fold_value {α β : Type} {n : ℕ} (f : α → Fin n → α) (g : β → Fin n → β)
    (v : α → β) (hv : ∀ x i, v (f x i) = g (v x) i) (a : α) :
    v (Fin.foldl n f a) = Fin.foldl n g (v a) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  exact (List.foldl_hom v (fun x i => (hv x i).symm)).symm

private theorem fold_magnitude {α : Type} {n : ℕ} (f : α → Fin n → α)
    (v : α → ℕ) (C : ℕ) (hv : ∀ x i, v (f x i) ≤ v x + C) (a : α) :
    v (Fin.foldl n f a) ≤ v a + n*C := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ]
    exact (ih (fun x i => f x i.succ) (fun x i => hv x i.succ) _).trans (by
      have hh := hv a 0
      rw [Nat.succ_mul]
      omega)

private def prefixOne {n : ℕ} (j : Fin n) (source : Vector ℤ n)
    (acc : SwapMeter (Vector ℤ n)) (t : Fin j.val) : SwapMeter (Vector ℤ n) :=
  let i : Fin n := ⟨t.val,t.isLt.trans j.isLt⟩
  ⟨acc.value.set i (source.get i),acc.arithmetic,acc.reads+1,acc.writes+1,acc.registers⟩

private def prefixRun {n : ℕ} (j : Fin n) (source row : Vector ℤ n) :
    SwapMeter (Vector ℤ n) :=
  Fin.foldl j.val (prefixOne j source) ⟨row,0,0,0,[]⟩

private theorem prefixRun_value {n : ℕ} (j : Fin n) (source row : Vector ℤ n) :
    (prefixRun j source row).value = Fin.foldl j.val (fun v t =>
      let i : Fin n := ⟨t.val,t.isLt.trans j.isLt⟩
      v.set i (source.get i)) row := by
  apply fold_value _ _ SwapMeter.value
  intros; rfl

private theorem prefixRun_cost {n : ℕ} (j : Fin n) (source row : Vector ℤ n) :
    (prefixRun j source row).arithmetic ≤ 0 ∧
    (prefixRun j source row).reads ≤ j.val ∧ (prefixRun j source row).writes ≤ j.val := by
  unfold prefixRun
  refine ⟨?_,?_,?_⟩
  · simpa using fold_magnitude (prefixOne j source) SwapMeter.arithmetic 0 (fun _ _ => le_rfl) (⟨row,0,0,0,[]⟩ : SwapMeter _)
  · simpa using fold_magnitude (prefixOne j source) SwapMeter.reads 1 (fun _ _ => le_rfl) (⟨row,0,0,0,[]⟩ : SwapMeter _)
  · simpa using fold_magnitude (prefixOne j source) SwapMeter.writes 1 (fun _ _ => le_rfl) (⟨row,0,0,0,[]⟩ : SwapMeter _)

private def afterPrefix {n : ℕ} (M : Hex.Matrix ℤ n n) (i j : Fin n) (source : Vector ℤ n) :
    SwapMeter (Hex.Matrix ℤ n n) :=
  let r := prefixRun j source (M.getRow i)
  ⟨M.modifyRow i (fun _ => r.value), r.arithmetic,r.reads,r.writes,r.registers⟩

private theorem modify_const {n : ℕ} (M : Hex.Matrix ℤ n n) (i : Fin n)
    (f : Vector ℤ n → Vector ℤ n) :
    M.modifyRow i (fun _ => f (M.getRow i)) = M.modifyRow i f := by
  apply Hex.Matrix.ext_getElem
  intro a b
  change ((M.modifyRow i.val _).getRow a).get b = ((M.modifyRow i.val _).getRow a).get b
  by_cases h : i = a
  · subst a
    simp
  · have hne : i.val ≠ a.val := fun h' => h (Fin.ext h')
    simp [hne]

private theorem afterPrefix_val {n : ℕ} (M : Hex.Matrix ℤ n n) (i j : Fin n) (source : Vector ℤ n) :
    (afterPrefix M i j source).value = M.modifyRow i (fun row => Fin.foldl j.val
      (fun v t =>
        let a : Fin n := ⟨t.val,t.isLt.trans j.isLt⟩
        v.set a (source.get a)) row) := by
  unfold afterPrefix
  simp only [prefixRun_value]
  exact modify_const ..

private def tailOne {n : ℕ} (k j : Fin n) (prev next : ℕ) (B : ℤ) (d : ℕ)
    (pairs : Vector (ℤ × ℤ) n) (s : SwapMeter (Hex.Matrix ℤ n n)) (i : Fin n) :
    SwapMeter (Hex.Matrix ℤ n n) :=
  if k.val < i.val then
    let (a,b) := pairs.get i
    let t := tailArithmetic prev next B d a b
    ⟨s.value.modifyRow i (fun row => (row.set j t.value.1).set k t.value.2),
      s.arithmetic+t.arithmetic, s.reads+2, s.writes+2,s.registers++t.registers⟩
  else s

private def tailMatrixOne {n : ℕ} (k j : Fin n) (prev next : ℕ) (B : ℤ) (d : ℕ)
    (pairs : Vector (ℤ × ℤ) n) (mat : Hex.Matrix ℤ n n) (i : Fin n) : Hex.Matrix ℤ n n :=
  if _ : k.val < i.val then
    let (a,b) := pairs.get i
    mat.modifyRow i (fun row =>
      (row.set j (((prev : ℤ)*a+B*b)/d)).set k (((next : ℤ)*b-B*a)/d))
  else mat

private theorem tailFold_value {n : ℕ} (k j : Fin n) (prev next : ℕ) (B : ℤ) (d : ℕ)
    (pairs : Vector (ℤ × ℤ) n) (s : SwapMeter (Hex.Matrix ℤ n n)) :
    (Fin.foldl n (tailOne k j prev next B d pairs) s).value =
      Fin.foldl n (tailMatrixOne k j prev next B d pairs) s.value := by
  apply fold_value
  intro x t
  unfold tailOne tailMatrixOne
  split <;> rfl

/-- Observe the native execution, including prefix copies and the two old entries
prefetched for each later row. The Gram slot and the basis-row swap stay separate
from the coefficient-table counters. -/
def nativeSwapMeter {n m : ℕ} (s : LLLState n m) (k : ℕ) : SwapMeter (LLLState n m) :=
  if hk : k < n then
    if hp : 0 < k then
      let i : Fin n := ⟨k,hk⟩
      let j := Hex.GramSchmidt.prevRow i hp
      let B := (s.ν.getRow i).get j
      let prev := s.d.get j.castSucc
      let d := s.d.get i.castSucc
      let next := s.d.get i.succ
      let p := pivotArithmetic prev next B d
      let a := afterPrefix s.ν j j (s.ν.getRow i)
      let b := afterPrefix a.value i j (s.ν.getRow j)
      let pivot := LLLState.setEntry b.value i j B
      let pairs : Vector (ℤ × ℤ) n := Vector.ofFn fun u =>
        if k < u.val then ((s.ν.getRow u).get i,(s.ν.getRow u).get j) else (0,0)
      let init : SwapMeter (Hex.Matrix ℤ n n) :=
        ⟨pivot,p.arithmetic+a.arithmetic+b.arithmetic,1+a.reads+b.reads,1+a.writes+b.writes,p.registers⟩
      let r := Fin.foldl n (tailOne i j prev next B d pairs) init
      ⟨⟨Hex.GramSchmidt.Int.adjacentSwap s.b i hp,r.value,
            s.d.set k p.value (h := Nat.lt_succ_of_lt hk)⟩,r.arithmetic,r.reads,r.writes,r.registers⟩
    else ⟨s,0,0,0,[]⟩
  else ⟨s,0,0,0,[]⟩

/-- The matrix-and-determinant state observed by the instrumented program is the actual native swap. -/
theorem nativeSwapMeter_state {n m : ℕ} (s : LLLState n m) (k : ℕ) :
    (nativeSwapMeter s k).value = s.swapStep k := by
  unfold nativeSwapMeter LLLState.swapStep
  split <;> rename_i hk
  · split <;> rename_i hp
    · simp only [pivotArithmetic_eq,tailFold_value,afterPrefix_val]
      rfl
    · rfl
  · rfl

/-- At most four pivot plus eight integer arithmetic operations per later row.
There is one pivot access and at most four coefficient-table reads and writes per row. -/
theorem nativeSwapMeter_cost {n m : ℕ} (s : LLLState n m) (k : ℕ) :
    (nativeSwapMeter s k).arithmetic ≤ 4+8*n ∧
    (nativeSwapMeter s k).reads ≤ 1+4*n ∧ (nativeSwapMeter s k).writes ≤ 1+4*n := by
  unfold nativeSwapMeter
  split <;> rename_i hk
  · split <;> rename_i hp
    · let i : Fin n := ⟨k,hk⟩
      let j := Hex.GramSchmidt.prevRow i hp
      let B := (s.ν.getRow i).get j
      let prev := s.d.get j.castSucc
      let d := s.d.get i.castSucc
      let next := s.d.get i.succ
      let p := pivotArithmetic prev next B d
      let a := afterPrefix s.ν j j (s.ν.getRow i)
      let b := afterPrefix a.value i j (s.ν.getRow j)
      let pivot := LLLState.setEntry b.value i j B
      let pairs : Vector (ℤ × ℤ) n := Vector.ofFn fun u =>
        if k < u.val then ((s.ν.getRow u).get i,(s.ν.getRow u).get j) else (0,0)
      let init : SwapMeter (Hex.Matrix ℤ n n) :=
        ⟨pivot,p.arithmetic+a.arithmetic+b.arithmetic,1+a.reads+b.reads,1+a.writes+b.writes,p.registers⟩
      let f := tailOne i j prev next B d pairs
      change (Fin.foldl n f init).arithmetic ≤ _ ∧ (Fin.foldl n f init).reads ≤ _ ∧
        (Fin.foldl n f init).writes ≤ _
      have hh : p.arithmetic = 4 := congrArg SwapMeter.arithmetic (pivotArithmetic_eq prev next B d)
      have ha : a.arithmetic ≤ 0 ∧ a.reads ≤ j.val ∧ a.writes ≤ j.val :=
        prefixRun_cost j _ _
      have hb : b.arithmetic ≤ 0 ∧ b.reads ≤ j.val ∧ b.writes ≤ j.val :=
        prefixRun_cost j _ _
      have hia : init.arithmetic ≤ 4 := by change p.arithmetic+a.arithmetic+b.arithmetic ≤ 4; omega
      have hir : init.reads ≤ 1+2*n := by change 1+a.reads+b.reads ≤ 1+2*n; have := j.isLt; omega
      have hiw : init.writes ≤ 1+2*n := by change 1+a.writes+b.writes ≤ 1+2*n; have := j.isLt; omega
      have ar := fold_magnitude f SwapMeter.arithmetic 8 (by
        intro x t; dsimp only [f,tailOne]; split <;> simp [tailArithmetic_eq]) init
      have re := fold_magnitude f SwapMeter.reads 2 (by
        intro x t; dsimp only [f,tailOne]; split <;> simp) init
      have wr := fold_magnitude f SwapMeter.writes 2 (by
        intro x t; dsimp only [f,tailOne]; split <;> simp) init
      omega
    · simp
  · simp

private def RegisterBound (H : ℕ) (xs : List ℤ) : Prop :=
  ∀ x ∈ xs, x.natAbs ≤ 2*(H*H)

private theorem mul_magnitude {H : ℕ} {a b : ℤ} (ha : a.natAbs ≤ H) (hb : b.natAbs ≤ H) :
    (a*b).natAbs ≤ H*H := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul ha hb

private theorem add_magnitude {H : ℕ} {a b : ℤ} (ha : a.natAbs ≤ H*H) (hb : b.natAbs ≤ H*H) :
    (a+b).natAbs ≤ 2*(H*H) :=
  (Int.natAbs_add_le ..).trans (by omega)

private theorem sub_magnitude {H : ℕ} {a b : ℤ} (ha : a.natAbs ≤ H*H) (hb : b.natAbs ≤ H*H) :
    (a-b).natAbs ≤ 2*(H*H) := by
  rw [sub_eq_add_neg]
  exact add_magnitude ha (by simpa using hb)

private theorem pivot_registerBound {H prev next : ℕ} {B : ℤ} (d : ℕ)
    (hprev : prev ≤ H) (hnext : next ≤ H) (hB : B.natAbs ≤ H) :
    RegisterBound H (pivotArithmetic prev next B d).registers := by
  have hprod := mul_magnitude (by simpa using hnext : (next : ℤ).natAbs ≤ H)
    (by simpa using hprev : (prev : ℤ).natAbs ≤ H)
  have hsquare : (B^2).natAbs ≤ H*H := by simpa only [pow_two] using mul_magnitude hB hB
  have hnum := add_magnitude hprod hsquare
  have hdiv := (Int.natAbs_ediv_le_natAbs ((next : ℤ)*prev+B^2) d).trans hnum
  rw [pivotArithmetic_eq]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> omega

private theorem tail_registerBound {H prev next : ℕ} {B a b : ℤ} (d : ℕ)
    (hprev : prev ≤ H) (hnext : next ≤ H) (hB : B.natAbs ≤ H)
    (ha : a.natAbs ≤ H) (hb : b.natAbs ≤ H) :
    RegisterBound H (tailArithmetic prev next B d a b).registers := by
  have hp := mul_magnitude (by simpa using hprev : (prev : ℤ).natAbs ≤ H) ha
  have hq := mul_magnitude hB hb
  have hr := mul_magnitude (by simpa using hnext : (next : ℤ).natAbs ≤ H) hb
  have ht := mul_magnitude hB ha
  have hleft := add_magnitude hp hq
  have hright := sub_magnitude hr ht
  have hdivl := (Int.natAbs_ediv_le_natAbs ((prev : ℤ)*a+B*b) d).trans hleft
  have hdivr := (Int.natAbs_ediv_le_natAbs ((next : ℤ)*b-B*a) d).trans hright
  rw [tailArithmetic_eq]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem fold_predicate {α : Type} {n : ℕ} (f : α → Fin n → α)
    (P : α → Prop) (step : ∀ x i, P x → P (f x i)) (a : α) (ha : P a) :
    P (Fin.foldl n f a) := by
  induction n generalizing a with
  | zero => simpa using ha
  | succ n ih =>
    rw [Fin.foldl_succ]
    exact ih (fun x i => f x i.succ) (fun x i => step x i.succ) _ (step a 0 ha)

private theorem tailFold_registerBound {n H : ℕ} (k j : Fin n) (prev next : ℕ) (B : ℤ)
    (d : ℕ) (pairs : Vector (ℤ × ℤ) n) (s : SwapMeter (Hex.Matrix ℤ n n))
    (hprev : prev ≤ H) (hnext : next ≤ H) (hB : B.natAbs ≤ H)
    (hpairs : ∀ i, k < i → (pairs.get i).1.natAbs ≤ H ∧ (pairs.get i).2.natAbs ≤ H)
    (hs : RegisterBound H s.registers) :
    RegisterBound H (Fin.foldl n (tailOne k j prev next B d pairs) s).registers := by
  apply fold_predicate _ (fun x => RegisterBound H x.registers) _ s hs
  intro state i hold
  unfold tailOne
  split <;> rename_i h
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hold x hx
    · exact tail_registerBound d hprev hnext hB (hpairs i h).1 (hpairs i h).2 _ hx
  · exact hold

/-- The very same evaluation records every intermediate integer. Bounding the stored
determinants and lower-triangular coefficients by H bounds all of these by 2 H². -/
theorem nativeSwapMeter_registers {n m H : ℕ} (s : LLLState n m) (k : ℕ)
    (hD : ∀ i, s.d.get i ≤ H) (hN : ∀ i j : Fin n, j < i → ((s.ν.getRow i).get j).natAbs ≤ H)
    (x : ℤ) (hx : x ∈ (nativeSwapMeter s k).registers) : x.natAbs ≤ 2*(H*H) := by
  suffices all : RegisterBound H (nativeSwapMeter s k).registers from all _ hx
  unfold nativeSwapMeter
  split <;> rename_i hk
  · split <;> rename_i hp
    · let i : Fin n := ⟨k,hk⟩
      let j := Hex.GramSchmidt.prevRow i hp
      have hji : j < i := by change k-1 < k; omega
      have hB := hN i j hji
      apply tailFold_registerBound _ _ _ _ _ _ _ _ (hD _) (hD _) hB
      · intro t ht
        have he {α : Type} (f : Fin n → α) : (Vector.ofFn f).get t = f t :=
          Vector.getElem_ofFn t.isLt
        have hkt : k < t.val := ht
        simp only [he,ite_eq_left hkt]
        exact ⟨hN t i ht, hN t j (hji.trans ht)⟩
      · exact pivot_registerBound _ (hD _) (hD _) hB
    · simp [RegisterBound]
  · simp [RegisterBound]

/-- Binary size of every multiplication, addition, subtraction and exact-division
result in the native swap, including its two numerators before division. -/
theorem nativeSwapMeter_register_size {n m L : ℕ} (s : LLLState n m) (k : ℕ)
    (hD : ∀ i, s.d.get i ≤ 2^L)
    (hN : ∀ i j : Fin n, j < i → ((s.ν.getRow i).get j).natAbs ≤ 2^L)
    (x : ℤ) (hx : x ∈ (nativeSwapMeter s k).registers) : x.natAbs.size ≤ 2*L+2 := by
  apply Nat.size_le.mpr
  calc
    x.natAbs ≤ 2*(2^L*2^L) := nativeSwapMeter_registers s k hD hN x hx
    _ = 2^(L+L+1) := by rw [pow_succ, pow_add]; ac_rfl
    _ < 2^(2*L+2) := Nat.pow_lt_pow_right (by decide) (by omega)

private def UpperFrame {n : ℕ} (A B : Hex.Matrix ℤ n n) : Prop :=
  ∀ i j : Fin n, i ≤ j → (A.getRow i).get j = (B.getRow i).get j

private theorem upperFrame_trans {n : ℕ} {A B C : Hex.Matrix ℤ n n}
    (h : UpperFrame A B) (g : UpperFrame B C) : UpperFrame A C :=
  fun i j hij => (h i j hij).trans (g i j hij)

private theorem set_get_other {n : ℕ} (v : Vector ℤ n) (i j : Fin n) (x : ℤ)
    (h : i < j) : (v.set i x).get j = v.get j :=
  Vector.getElem_set_ne i.isLt j.isLt (Nat.ne_of_lt h)

private theorem upper_modify {n : ℕ} (M : Hex.Matrix ℤ n n) (r : Fin n)
    (f : Vector ℤ n → Vector ℤ n)
    (h : ∀ j : Fin n, r ≤ j → (f (M.getRow r)).get j = (M.getRow r).get j) :
    UpperFrame (M.modifyRow r f) M := by
  intro i j hij
  by_cases hr : r = i
  · subst i
    rw [Hex.Matrix.getRow_modifyRow_self]
    exact h j hij
  · rw [Hex.Matrix.getRow_modifyRow_ne _ _ _ _ (fun he => hr (Fin.ext he))]

private theorem prefix_upper {n : ℕ} (j c : Fin n) (source row : Vector ℤ n) (hc : j ≤ c) :
    (prefixRun j source row).value.get c = row.get c := by
  unfold prefixRun
  apply fold_predicate (prefixOne j source) (fun z : SwapMeter (Vector ℤ n) => z.value.get c = row.get c) _ _ rfl
  intro z t hz
  let u : Fin n := ⟨t.val,t.isLt.trans j.isLt⟩
  change (z.value.set u (source.get u)).get c = _
  have huc : u < c := t.isLt.trans_le (show j.val ≤ c.val from hc)
  exact (set_get_other z.value u c (source.get u) huc).trans hz

private theorem afterPrefix_upper {n : ℕ} (M : Hex.Matrix ℤ n n) (r j : Fin n)
    (source : Vector ℤ n) (h : j ≤ r) : UpperFrame (afterPrefix M r j source).value M :=
  upper_modify _ _ _ (fun c hc => prefix_upper j c source _ (h.trans hc))

private theorem setEntry_upper {n : ℕ} (M : Hex.Matrix ℤ n n) (k j : Fin n) (v : ℤ)
    (h : j < k) : UpperFrame (LLLState.setEntry M k j v) M :=
  upper_modify _ _ _ (fun _ hc => set_get_other _ _ _ _ (h.trans_le hc))

private theorem tailOne_upper {n : ℕ} (k j : Fin n) (prev next : ℕ) (B : ℤ) (d : ℕ)
    (pairs : Vector (ℤ × ℤ) n) (s : SwapMeter (Hex.Matrix ℤ n n)) (i : Fin n) (h : j < k) :
    UpperFrame (tailOne k j prev next B d pairs s i).value s.value := by
  unfold tailOne
  split <;> rename_i hki
  · apply upper_modify
    intro c hc
    have hkc : k < c := lt_of_lt_of_le hki hc
    exact (set_get_other _ _ _ _ hkc).trans (set_get_other _ _ _ _ (h.trans hkc))
  · exact fun _ _ _ => rfl

/-- The full native swap leaves every diagonal and strict-upper coefficient untouched.
This also applies to slots not constrained by the native state validity predicate. -/
theorem native_swap_upper_frame {n m : ℕ} (s : LLLState n m) (k : ℕ) (i j : Fin n) (hij : i ≤ j) :
    (s.swapStep k).ν[i][j] = s.ν[i][j] := by
  suffices hall : UpperFrame (nativeSwapMeter s k).value.ν s.ν by
    change ((s.swapStep k).ν.getRow i).get j = (s.ν.getRow i).get j
    rw [← nativeSwapMeter_state]
    exact hall i j hij
  unfold nativeSwapMeter
  split <;> rename_i hk
  · split <;> rename_i hp
    · let r : Fin n := ⟨k,hk⟩
      let a := Hex.GramSchmidt.prevRow r hp
      have har : a < r := by change k-1 < k; omega
      dsimp only
      apply fold_predicate (tailOne r a _ _ _ _ _) (fun q : SwapMeter (Hex.Matrix ℤ n n) => UpperFrame q.value s.ν)
      · intro q t hq
        exact upperFrame_trans (tailOne_upper _ _ _ _ _ _ _ _ _ har) hq
      · exact upperFrame_trans (setEntry_upper _ _ _ _ har)
          (upperFrame_trans (afterPrefix_upper _ _ _ _ har.le) (afterPrefix_upper _ _ _ _ le_rfl))
    · exact fun _ _ _ => rfl
  · exact fun _ _ _ => rfl

end Lattice
end LinearProgramming
end Optimization
end OAI
