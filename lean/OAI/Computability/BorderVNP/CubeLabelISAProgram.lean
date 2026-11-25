import OAI.Computability.BorderVNP.CubeLabelISASelect
import Mathlib.Algebra.BigOperators.Intervals

/-! # Traversal and memory readback of the native cube-label program

Each cell first scans every label. It commits the winning trial's bin numerators,
stores the winning word at the cell's own address, and advances its ordinal.
Per-cell costs are summed over the remaining public ordinals, allowing the work
to depend on the individual incidence-list lengths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private def storeLabel : Code := .block [
  .binary .add 22 21 1, .store 22 17, .binary .add 1 1 20]

/-- Select the first minimum, commit its bin cache, and write the label to memory. -/
def step (candidate commit : Code) : Code :=
  .block [select candidate,.copy 2 17,commit,storeLabel]

/-- Iterate from the current cell ordinal in register 1 to the exclusive bound in 19. -/
def assign (candidate commit : Code) : Code := .whileLt 1 19 (step candidate commit)

/-- The surrounding cell traversal adds writes to the cell counter, address
scratch, cursor, and incumbents of the label selector. -/
theorem assign_keeps {a b : Code} {r : Reg} (ha : a.keeps r = true) (hb : b.keeps r = true)
    (h₁ : r ≠ 1) (h₂ : r ≠ 2) (h₁₇ : r ≠ 17) (h₁₈ : r ≠ 18) (h₂₂ : r ≠ 22) :
    (assign a b).keeps r = true := by
  simp [assign,step,storeLabel,Code.block,Code.keeps,select_keeps ha h₂ h₁₇ h₁₈,hb,h₁,h₂,h₂₂]

/-- Deterministic trial and commit code give a deterministic cell traversal. -/
theorem assign_deterministic {a b : Code} (ha : a.deterministic = true)
    (hb : b.deterministic = true) : (assign a b).deterministic = true := by
  simp [assign,step,storeLabel,Code.block,Code.deterministic,select_deterministic ha,hb]

variable {w z cells base : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
  {a b : Code} {trialCost commitCost : ℕ → ℕ} {f : ℕ → Fin (z+1) → ℕ}
  {Ready : Bank w → Prop} {Image Committed : ℕ → Memory w → Prop}

/-- Interface between the cell loop and the fitted scoring and cache fragments.
The two memory images describe the state before a cell and immediately after
committing its cache. Writing its selected label links the latter to the next cell. -/
structure AssignmentPass (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (a b : Code) (cells base : ℕ) (trialCost commitCost : ℕ → ℕ) (f : ℕ → Fin (z+1) → ℕ)
    (Ready : Bank w → Prop) (Image Committed : ℕ → Memory w → Prop) : Prop where
  /-- Fixed bound, unit increment and base address of the label array. -/
  values : ∀ s, Ready s → (s 19).val = cells ∧ (s 20).val = 1 ∧ (s 21).val = base
  /-- Scratch assignments of the outer loop preserve the static parameters. -/
  write : ∀ s, Ready s → ∀ r : Reg, r = 1 ∨ r = 2 ∨ r = 22 → ∀ v, Ready (Function.update s r v)
  /-- Each label store fits in the word-addressed array. -/
  room : ∀ c < cells, base+c < 2^w
  /-- Every trial at the current physical cache computes the corresponding score. -/
  trial : ∀ c < cells, ∀ m, Image c m →
    SelectionTrial pub macros m a (trialCost c) (f c) (fun s => Ready s ∧ (s 1).val = c)
  /-- The bin commit leaves the current ordinal and winning label in place. -/
  keeps : b.keeps 1 = true ∧ b.keeps 17 = true
  /-- Committing the winner updates the cache and preserves already assigned label words. -/
  commit : ∀ c < cells, ∀ s m, Ready s → (s 1).val = c → Image c m →
    (s 2).val = (Cube.firstMinimum (f c)).val →
    ∃ es t mt, Runs pub macros b s m es t mt ∧ traceCost es ≤ commitCost c ∧
      Ready t ∧ Committed c mt ∧ ∀ j < c, mt (base+j) = m (base+j)
  /-- The single label store produces the next mathematical prefix and cache image. -/
  advance : ∀ c < cells, ∀ m, Committed c m → ∀ v : Word w, v.val = (Cube.firstMinimum (f c)).val →
    Image (c+1) (Function.update m (base+c) v)

/-- Prefix of the public labels already realized at their true word addresses. -/
def Prefix (base : ℕ) (f : ℕ → Fin (z+1) → ℕ) (c : ℕ) (m : Memory w) : Prop :=
  ∀ j < c, (m (base+j)).val = (Cube.firstMinimum (f j)).val

private theorem append_prefix {m m' : Memory w} {c : ℕ} (h : Prefix base f c m)
    (old : ∀ j < c, m' (base+j) = m (base+j)) {v : Word w}
    (hv : v.val = (Cube.firstMinimum (f c)).val) :
    Prefix base f (c+1) (Function.update m' (base+c) v) := by
  intro j hj
  by_cases he : j = c
  · simpa [he] using hv
  · have hl : j < c := by omega
    rw [Function.update_of_ne (show base+j ≠ base+c by omega),old j hl]
    exact h j hl

private theorem store_run (ctx : AssignmentPass pub macros a b cells base trialCost commitCost f Ready Image Committed)
    {c : ℕ} (hc : c < cells) (s : Bank w) (m : Memory w) (hr : Ready s)
    (h₁ : (s 1).val = c) :
    ∃ es t, Runs pub macros storeLabel s m es t (Function.update m (base+c) (s 17)) ∧
      traceCost es = 3 ∧ Ready t ∧ (t 1).val = c+1 := by
  let addr := s 21 + s 1
  let u := Function.update s 22 addr
  have rv : Runs pub macros (.binary .add 22 21 1) s m [tick w] u m := Runs.localStep m rfl rfl
  have hu : Ready u := ctx.write _ hr 22 (by simp) _
  have huaddr : (u 22).val = base+c := by
    simp only [u,Function.update_self,addr,Fin.val_add,(ctx.values s hr).2.2,h₁,
      Nat.mod_eq_of_lt (ctx.room c hc)]
  have huword : u 17 = s 17 := Function.update_of_ne (by decide) ..
  have sw := Runs.store pub macros 22 17 u m
  rw [huaddr,huword] at sw
  let t := Function.update u 1 (u 1 + u 20)
  let m' := Function.update m (base+c) (s 17)
  have inc : Runs pub macros (.binary .add 1 1 20) u m' [tick w] t m' := Runs.localStep m' rfl rfl
  have hu₁ : (u 1).val = c := by simpa (config := {decide := true}) [u] using h₁
  have fit : cells < 2^w := (ctx.values s hr).1 ▸ (s 19).isLt
  refine ⟨_,t,rv.seq (sw.seq inc),rfl,ctx.write _ hu 1 (by simp) _,?_⟩
  simp only [t,Function.update_self,Fin.val_add,hu₁,(ctx.values u hu).2.1,
    Nat.mod_eq_of_lt (show c+1 < 2^w by omega)]

/-- Tick allowance of one cell, including its loop guard. Only the incidence
costs for the current cell enter this expression. -/
def cellTicks (z : ℕ) (trialCost commitCost : ℕ → ℕ) (c : ℕ) : ℕ :=
  (z+1)*(trialCost c+5)+4 + commitCost c + 5

/-- One cell's native trace establishes the next cache image and the extended
prefix of least-minimum labels. The allowance includes its enclosing loop guard. -/
theorem step_run (ctx : AssignmentPass pub macros a b cells base trialCost commitCost f Ready Image Committed)
    {c : ℕ} (hc : c < cells) (s : Bank w) (m : Memory w) (hr : Ready s)
    (h₁ : (s 1).val = c) (image : Image c m) (pre : Prefix base f c m) :
    ∃ es t mt, Runs pub macros (step a b) s m es t mt ∧
      1+traceCost es ≤ cellTicks z trialCost commitCost c ∧ Ready t ∧
      (t 1).val = c+1 ∧ Image (c+1) mt ∧ Prefix base f (c+1) mt := by
  obtain ⟨es,u,sel,et,⟨hu,hu₁⟩,hwin,_⟩ := select_run (ctx.trial c hc m image) s ⟨hr,h₁⟩
  let v := Function.update u 2 (u 17)
  have copy : Runs pub macros (.copy 2 17) u m [tick w] v m := Runs.localStep m rfl rfl
  have hv := ctx.write u hu 2 (by simp) (u 17)
  have hv₁ : (v 1).val = c := by simpa (config := {decide := true}) [v] using hu₁
  have hv₂ : (v 2).val = (Cube.firstMinimum (f c)).val := by simpa [v] using hwin
  obtain ⟨fs,p,mp,com,ft,hp,im',old⟩ := ctx.commit c hc v m hv hv₁ image hv₂
  have hp₁ := (congrArg Fin.val (com.keepsReg ctx.keeps.1)).trans hv₁
  have hp₁₇ : (p 17).val = (Cube.firstMinimum (f c)).val := by
    rw [com.keepsReg ctx.keeps.2]
    simpa (config := {decide := true}) [v] using hwin
  obtain ⟨gs,t,st,gt,ht,ht₁⟩ := store_run ctx hc p mp hp hp₁
  refine ⟨_,t,_,sel.seq (copy.seq (com.seq st)),?_,ht,ht₁,ctx.advance c hc mp im' _ hp₁₇,
    append_prefix pre old hp₁₇⟩
  simp only [traceCost,VPVNP.RAMBuckets.cost_append]
  change 1+(traceCost es + (1+(traceCost fs + traceCost gs))) ≤ _
  unfold cellTicks
  omega

/-- The outer program returns after the last cell. Readback at each address is
exactly the first minimizing label for that stage's score, with the final cache
image present in the same memory. Its total work is the sum of the actual
per-cell allowances and the terminating guard. -/
theorem assign_run (ctx : AssignmentPass pub macros a b cells base trialCost commitCost f Ready Image Committed)
    {c : ℕ} (hc : c ≤ cells) (s : Bank w) (m : Memory w) (hr : Ready s)
    (h₁ : (s 1).val = c) (image : Image c m) (pre : Prefix base f c m) :
    ∃ es t mt, Runs pub macros (assign a b) s m es t mt ∧
      traceCost es ≤ (∑ j ∈ Finset.Ico c cells, cellTicks z trialCost commitCost j)+1 ∧
      Ready t ∧ (t 1).val = cells ∧ Image cells mt ∧ Prefix base f cells mt := by
  by_cases live : c < cells
  · have guard : s 1 < s 19 := Fin.lt_def.mpr (by simpa only [h₁,(ctx.values s hr).1] using live)
    obtain ⟨es,u,mu,one,et,hu,hu₁,im',pre'⟩ := step_run ctx live s m hr h₁ image pre
    obtain ⟨fs,t,mt,rest,ft,ht,ht₁,im'',pre''⟩ := assign_run ctx live u mu hu hu₁ im' pre'
    refine ⟨_,t,mt,Runs.whileStep guard one rest,?_,ht,ht₁,im'',pre''⟩
    change 1+traceCost (es++fs) ≤ _
    simp only [traceCost,VPVNP.RAMBuckets.cost_append,Finset.sum_eq_sum_Ico_succ_bot live]
    change 1+(traceCost es + traceCost fs) ≤ _
    change traceCost fs ≤ (∑ j ∈ Finset.Ico (c+1) cells, cellTicks z trialCost commitCost j)+1 at ft
    omega
  · obtain rfl : c = cells := by omega
    have guard : ¬ s 1 < s 19 := by simp only [Fin.lt_def,h₁,(ctx.values s hr).1,lt_self_iff_false,not_false_eq_true]
    exact ⟨_,s,m,Runs.whileDone guard,by simp; rfl,hr,h₁,image,pre⟩
termination_by cells-c

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
