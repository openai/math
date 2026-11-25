import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Native construction of the cube declaration's column totals

The two counted loops sum the actual claimed row words and store one total
per coordinate. A column accumulator occupies one register; the claimed
row array is preserved. These totals subsequently undergo the least-minimum
check and are derived entirely from the decoded common declaration.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderTotals

open VPVNP.BurstRAM Finset

/-- Prefix of the `j`-th column in the row-major claimed table. -/
def sumAt (mem : ℕ → ℕ) (base dim j k : ℕ) : ℕ :=
  ∑ l ∈ range k, mem (base+l*dim+j)

/-- Shared memory after storing the first `columns` totals. -/
def image (mem : ℕ → ℕ) (base target dim rows columns : ℕ) (x : ℕ) :=
  if target ≤ x ∧ x < target+columns then sumAt mem base dim (x-target) rows else mem x

private theorem store_image (mem : ℕ → ℕ) (base target dim rows j : ℕ) :
    Function.update (image mem base target dim rows j) (target+j) (sumAt mem base dim j rows) =
      image mem base target dim rows (j+1) := by
  funext x
  by_cases he : x = target+j
  · subst x
    simp [image]
  · rw [Function.update_of_ne he]
    have same : (target ≤ x ∧ x < target+j) ↔ (target ≤ x ∧ x < target+(j+1)) := by omega
    simp only [image, same]

/-- Setup for scanning the dense table in column order. -/
def init : Code := .block [.constant 36 1, .constant 37 0]

/-- Reset the row cursor and the column accumulator. -/
def beginColumn : Code := .block [.constant 38 0, .constant 39 0]

/-- Read a single claimed row word and add it to the running column sum. -/
def entry : Code := .block [.binary .mul 40 38 32, .binary .add 40 30 40,
  .binary .add 40 40 37, .load 41 40, .binary .add 39 39 41, .binary .add 38 38 36]

/-- Write a completed column and advance the coordinate cursor. -/
def endColumn : Code := .block [.binary .add 40 31 37, .store 40 39, .binary .add 37 37 36]

/-- One column visits exactly the row count stored in register 33. -/
def column : Code := .seq beginColumn (.seq (.whileLt 38 33 entry) endColumn)

/-- Native table pass, given claimed and total bases in 30 and 31, dimension in
32, and row count in 33. -/
def program : Code := .seq init (.whileLt 37 32 column)

/-- The exact upper bound from the loop guards, arithmetic, probes, and stores. -/
def cost (dim rows : ℕ) : ℕ := 3+dim*(7*rows+7)

private def ready (base target dim rows : ℕ) (z : NatState) :=
  z.reg 30 = base ∧ z.reg 31 = target ∧ z.reg 32 = dim ∧ z.reg 33 = rows ∧ z.reg 36 = 1

private theorem ready_keep {base target dim rows : ℕ} {z : NatState} {c : Code} (env : Arg → ℕ)
    (h : ready base target dim rows z) (pr : c.protects 37 = true) :
    ready base target dim rows (c.fixedEval env z) :=
  ⟨(c.fixedEval_protected _ z pr 30 (by decide)).trans h.1,
    (c.fixedEval_protected _ z pr 31 (by decide)).trans h.2.1,
    (c.fixedEval_protected _ z pr 32 (by decide)).trans h.2.2.1,
    (c.fixedEval_protected _ z pr 33 (by decide)).trans h.2.2.2.1,
    (c.fixedEval_protected _ z pr 36 (by decide)).trans h.2.2.2.2⟩

/-- Execute the complete sparse public header pass. Every claimed word is
read exactly once and each returned total is the corresponding mathematical
column sum, including when the column or row count is zero. -/
theorem run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (base target dim rows cap : ℕ)
    (rb : (r 30).val = base) (rt : (r 31).val = target) (rd : (r 32).val = dim)
    (rr : (r 33).val = rows) (one : 1 < 2^w)
    (srcRoom : base+rows*dim ≤ 2^w) (dstRoom : target+dim ≤ 2^w)
    (sep : base+rows*dim ≤ target ∨ target+dim ≤ base)
    (wordRoom : rows*cap < 2^w)
    (bounded : ∀ j < dim, ∀ k < rows, readings m (base+k*dim+j) ≤ cap) :
    BoundedRun pub mac program r m (cost dim rows) fun z =>
      z.mem = image (readings m) base target dim rows dim := by
  let sums := sumAt (readings m) base dim
  let img := image (readings m) base target dim rows
  let P j z := ready base target dim rows z ∧ z.reg 37 = j ∧ z.mem = img j
  have preg j z (h : P j z) : z.reg 37 = j ∧ z.reg 32 = dim := ⟨h.2.1,h.1.2.2.1⟩
  have pstep j (hj : j < dim) (u : Bank w) (mm : Memory w) (hz : P j (.ofWords u mm)) :
      BoundedRun pub mac column u mm (7*rows+6) (P (j+1)) := by
    let Q k z := P j z ∧ z.reg 38 = k ∧ z.reg 39 = sums j k
    have qreg k z (h : Q k z) : z.reg 38 = k ∧ z.reg 33 = rows := ⟨h.2.1,h.1.1.2.2.2.1⟩
    have qstep k (hk : k < rows) (v : Bank w) (mv : Memory w) (hq : Q k (.ofWords v mv)) :
        BoundedRun pub mac entry v mv 6 (Q (k+1)) := by
      let z := NatState.ofWords v mv
      obtain ⟨⟨hr,h37,hm⟩,h38,h39⟩ := hq
      obtain ⟨h30,h31,h32,h33,h36⟩ := hr
      have stride : k*dim+j < rows*dim :=
        (Nat.add_lt_add_left hj _).trans_le (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right dim hk)
      have addr : base+k*dim+j < 2^w := by omega
      have keep : img j (base+k*dim+j) = readings m (base+k*dim+j) := by
        unfold img image
        rw [ite_eq_right (by omega)]
      have load : (NatState.ofWords v mv).mem (base+k*dim+j) = readings m (base+k*dim+j) := (congrFun hm _).trans keep
      have next : sums j (k+1) = sums j k + readings m (base+k*dim+j) := sum_range_succ ..
      have sumFit : sums j (k+1) < 2^w := by
        calc
          _ ≤ ∑ _ ∈ range (k+1), cap :=
            sum_le_sum fun l hl => bounded j hj l ((mem_range.mp hl).trans_le hk)
          _ = (k+1)*cap := by simp
          _ ≤ rows*cap := Nat.mul_le_mul_right cap hk
          _ < _ := wordRoom
      have safe : entry.fixedSafe w (readings pub) z := by
        have vfit : k+1 < 2^w := Nat.lt_of_le_of_lt hk (rr ▸ (r 33).isLt)
        simp (config := {decide := true}) [entry,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,
          Code.safeReadOnly,addressOpFits,addressOp,z,h30,h32,h36,h37,h38,h39,load]
        omega
      apply (entry.runFixed pub mac v mv safe).mono le_rfl
      rintro y rfl
      refine ⟨⟨ready_keep _ (z := z) ⟨h30,h31,h32,h33,h36⟩ (by decide),
        (entry.fixedEval_protected _ z (by decide : entry.protects 38 = true) 37 (by decide)).trans h37,hm⟩,?_,?_⟩ <;>
        simp (config := {decide := true}) [entry,Code.block,Code.fixedEval,Code.evalNat,addressOp,
          h30,h32,h36,h37,h38,h39,load,next]
    have start := beginColumn.runFixed pub mac u mm (by
      simp [beginColumn,Code.block,Code.fixedSafe,Code.safeReadOnly])
    have initQ (v : Bank w) (mv : Memory w) (h : NatState.ofWords v mv =
        beginColumn.fixedEval (readings pub) (.ofWords u mm)) : Q 0 (.ofWords v mv) := by
      rw [h]
      refine ⟨⟨ready_keep _ hz.1 (by decide),
        (beginColumn.fixedEval_protected _ _ (by decide : beginColumn.protects 38 = true) 37 (by decide)).trans hz.2.1,
        hz.2.2⟩,?_,?_⟩ <;> simp (config := {decide := true}) [beginColumn,Code.block,Code.fixedEval,Code.evalNat,sums,sumAt]
    have finish (v : Bank w) (mv : Memory w) (hq : Q rows (.ofWords v mv)) :
        BoundedRun pub mac endColumn v mv 3 (P (j+1)) := by
      let z := NatState.ofWords v mv
      obtain ⟨⟨hr,h37,hm⟩,_,h39⟩ := hq
      obtain ⟨h30,h31,h32,h33,h36⟩ := hr
      have safe : endColumn.fixedSafe w (readings pub) z := by
        have inc : j+1 < 2^w := Nat.lt_of_le_of_lt hj (rd ▸ (r 32).isLt)
        simp (config := {decide := true}) [endColumn,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,
          Code.safeReadOnly,addressOpFits,addressOp,z,h31,h36,h37]
        omega
      apply (endColumn.runFixed pub mac v mv safe).mono le_rfl
      rintro y rfl
      refine ⟨ready_keep _ (z := z) ⟨h30,h31,h32,h33,h36⟩ (by decide),?_,?_⟩
      · simp (config := {decide := true}) [endColumn,Code.block,Code.fixedEval,Code.evalNat,addressOp,h36,h37]
      · simp (config := {decide := true}) [endColumn,Code.block,Code.fixedEval,Code.evalNat,addressOp,h31,h37,h39,hm,
          img,sums,store_image]
    have stage := start.seq fun v mv hh => (run_counted_loop pub mac 38 33 entry rows 6 Q qreg qstep 0
      (Nat.zero_le _) v mv (initQ v mv hh)).seq finish
    exact stage.mono (by change 2+((rows-0)*(6+1)+1+3) ≤ _; omega) fun _ h => h
  have initial := init.runFixed pub mac r m (by
    change 1 < 2^w ∧ 0 < 2^w
    omega)
  have p0 (u : Bank w) (mm : Memory w) (he : NatState.ofWords u mm = init.fixedEval (readings pub) (.ofWords r m)) :
      P 0 (.ofWords u mm) := by
    rw [he]
    refine ⟨?_,?_,?_⟩
    · simp (config := {decide := true}) [ready,init,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,readings,rb,rt,rd,rr]
    · simp (config := {decide := true}) [init,Code.block,Code.fixedEval,Code.evalNat]
    · funext x
      simp [init,Code.block,Code.fixedEval,Code.evalNat,img,image,NatState.ofWords]
  have stage := initial.seq fun u mm he => run_counted_loop pub mac 37 32 column dim (7*rows+6) P
    preg pstep 0 (Nat.zero_le _) u mm (p0 u mm he)
  exact stage.mono (by unfold cost; change 2+((dim-0)*(7*rows+6+1)+1) ≤ _; rw [Nat.sub_zero]; exact le_of_eq (by ring)) fun _ h => h.2.2

end RoutingISA.HeaderTotals

end BorderVNP
end Computability
end OAI
