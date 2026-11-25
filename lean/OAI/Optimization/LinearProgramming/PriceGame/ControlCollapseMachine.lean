import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! A finite stack program for lifting a designated query through all ancestor price
tables. The polynomial bound uses the selection property of the median at every level. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

abbrev Row := List ℚ
abbrev RowState := ℕ × Row
def rowCode : Row → List Bool := listCode ratCode
def rowStateCode : RowState → List Bool := prodCode Nat.bits rowCode

def ascend (v : Row × RowState) : RowState :=
  (v.2.1 / 2, liftRow (v.2.1, v.1, v.2.2))

noncomputable def ascendP : Procedure (prodCode rowCode rowStateCode) rowStateCode ascend := by
  let base := first rowCode rowStateCode
  let state := second rowCode rowStateCode
  let index := (first Nat.bits rowCode).comp state
  let child := (second Nat.bits rowCode).comp state
  let parent := binaryDiv.comp (index.pair (constant _ Nat.bits 2))
  let row := liftRowP.comp (index.pair (base.pair child))
  exact (parent.pair row).congrFun (by intro v; rfl)

private theorem from_list (row : List ℚ) (i : ℕ) :
    (row.drop i).headD 0 = 0 ∨ (row.drop i).headD 0 ∈ row := by
  cases hh : row.drop i with
  | nil => exact Or.inl rfl
  | cons x rest => exact Or.inr (List.mem_of_mem_drop (hh ▸ List.mem_cons_self))

private theorem median_satisfies (P : ℚ → Prop) (a b c : ℚ) (ha : P a) (hb : P b) (hc : P c) :
    P (States.median₃ a b c) := by
  simp only [States.median₃, max_def, min_def]
  split_ifs <;> first | exact ha | exact hb | exact hc

private theorem liftCell_satisfies (P : ℚ → Prop) (hzero : P 0) (i : ℕ) (v : LiftContext)
    (hbase : ∀ z ∈ v.2.1, P z) (hchild : ∀ z ∈ v.2.2, P z) : P (liftCell v i) := by
  have get (r : Row) (j : ℕ) (hr : ∀ z ∈ r, P z) : P ((r.drop j).headD 0) := by
    rcases from_list r j with e | e
    · rw [e]; exact hzero
    · exact hr _ e
  simp only [liftCell]
  split
  · exact get _ _ hchild
  · exact median_satisfies _ _ _ _ (get _ _ hbase) (get _ _ hchild) (get _ _ hchild)

private def Within (B : ℕ) (s : RowState) : Prop :=
  s.1.bits.length ≤ B ∧ s.2.length ≤ B ∧ ∀ v ∈ s.2, (ratCode v).length ≤ B

private theorem ascend_within (B : ℕ) (z : (ratCode 0).length ≤ B) (r : Row) (s : RowState)
    (hr : r.length ≤ B) (hq : ∀ v ∈ r, (ratCode v).length ≤ B) (hs : Within B s) :
    Within B (ascend (r,s)) := by
  refine ⟨(bits_length_mono (Nat.div_le_self s.1 2)).trans hs.1, ?_, ?_⟩
  · simpa [ascend, liftRow] using hr
  · intro v hmem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
    exact liftCell_satisfies (fun q : ℚ => (ratCode q).length ≤ B) z i (s.1,r,s.2) hq hs.2.2

private theorem fold_within (B : ℕ) (z : (ratCode 0).length ≤ B) (rs : List Row) (s : RowState)
    (hr : ∀ r ∈ rs, r.length ≤ B ∧ ∀ v ∈ r, (ratCode v).length ≤ B) (hs : Within B s) :
    Within B (rs.foldl (fun t r => ascend (r,t)) s) := by
  induction rs generalizing s with
  | nil => exact hs
  | cons r rs ih =>
    have h := hr r List.mem_cons_self
    exact ih (ascend (r,s)) (fun row hm => hr row (List.mem_cons_of_mem _ hm))
      (ascend_within B z r s h.1 h.2 hs)

private theorem encoded_within (B : ℕ) (s : RowState) (hs : Within B s) :
    (rowStateCode s).length ≤ 2*B + 1 + B*(2*B+2) + 1 := by
  have hc := listCode_length_map_bound ratCode id s.2 B hs.2.2
  simp only [List.map_id] at hc
  have hmul := Nat.mul_le_mul_right (2*B+2) hs.2.1
  have hidx := hs.1
  simp only [rowStateCode, prodCode, pairBits_length, rowCode]
  omega

private theorem scan_bound (rs : List Row) (s : RowState) (i : ℕ) :
    let L := (listCode rowCode rs).length + (rowStateCode s).length
    let B := L + (ratCode 0).length + 1
    (rowStateCode ((rs.take i).foldl (fun t r => ascend (r,t)) s)).length ≤
      2*B+1+B*(2*B+2)+1 := by
  intro L B
  have hstate : (rowStateCode s).length ≤ L := Nat.le_add_left ..
  change (prodCode Nat.bits rowCode s).length ≤ L at hstate
  simp only [prodCode, pairBits_length] at hstate
  have hbase : (rowCode s.2).length ≤ B := by dsimp [B]; omega
  have hbits : s.1.bits.length ≤ B := by dsimp [B]; omega
  have hlength (r : Row) (hr : (rowCode r).length ≤ B) : r.length ≤ B :=
    (list_length_le_code ratCode r).trans hr
  have hscalar (r : Row) (hr : (rowCode r).length ≤ B) : ∀ v ∈ r, (ratCode v).length ≤ B :=
    fun v hv => (code_le_of_mem ratCode hv).trans hr
  apply encoded_within
  apply fold_within B (by dsimp [B]; omega)
  · intro r hr
    have hh := code_le_of_mem rowCode (List.mem_of_mem_take hr)
    have hrows : (listCode rowCode rs).length ≤ L := Nat.le_add_right ..
    have hrow : (rowCode r).length ≤ B := by dsimp [B]; omega
    exact ⟨hlength r hrow, hscalar r hrow⟩
  · exact ⟨hbits, hlength _ hbase, hscalar _ hbase⟩

/-- Consume the actual ancestor tables from deepest to root. The input stores them
chronologically; the first program reverses the table list before the reducer. -/
def collapse (v : List Row × RowState) : RowState :=
  v.1.reverse.foldl (fun s row => ascend (row,s)) v.2

noncomputable def collapseP : Procedure (prodCode (listCode rowCode) rowStateCode) rowStateCode collapse := by
  let p : Polynomial ℕ := Polynomial.X + Polynomial.C ((ratCode 0).length+1)
  let bound : Polynomial ℕ := 2*p+1+p*(2*p+2)+1
  let scan := foldList ([] : Row) ascendP bound (by
    intro rows s i
    simpa only [bound, p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C, Nat.add_assoc]
      using scan_bound rows s i)
  let rows := first (listCode rowCode) rowStateCode
  let s := second (listCode rowCode) rowStateCode
  exact (scan.comp (((listReverse rowCode ([] : Row)).comp rows).pair s)).congrFun (by intro v; rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
