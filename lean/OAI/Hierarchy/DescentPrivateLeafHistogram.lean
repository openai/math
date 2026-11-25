import OAI.Hierarchy.DescentOldOccurrenceHistogram
import OAI.Hierarchy.DescentTreePrefixIntervals

namespace OAI
/-! # One sparse arrival histogram serves all exceptional roots and their entire binary trees -/

namespace Hierarchy.DescentPrivateLeafHistogram
open DescentTreePrefixIntervals DescentOldOccurrenceRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {n B H w h : ℕ}

abbrev Arrival (B H : ℕ) := Option (Fin B×Fin (2^H))

/-- The last bucket absorbs all gated-off, paid-router and padded arrivals. -/
def number : Arrival B H→Fin (B*2^H+1)
  | none=>Fin.last _
  | some uv=>(finProdFinEquiv uv).castSucc

def hits (row : Arrival B H) (b : Fin B) (lo hi : ℕ) : Prop :=
  ∃v : Fin (2^H),row=some (b,v) ∧ lo≤v.val ∧ v.val<hi

theorem test (row : Arrival B H) (b : Fin B) {lo hi : ℕ} (_ordered : lo≤hi) (cap : hi≤2^H) :
    (b.val*2^H+lo≤(number row).val ∧ (number row).val<b.val*2^H+hi) ↔ hits row b lo hi := by
  have total:=Nat.mul_le_mul_right (2^H) b.isLt
  rw [Nat.succ_mul] at total
  cases row with
  | none=>
    change (_≤B*2^H ∧ B*2^H<_) ↔ _
    simp only [hits,reduceCtorEq,false_and,exists_false,iff_false]
    omega
  | some atRow=>
    obtain ⟨c,v⟩:=atRow
    have ord : (number (some (c,v))).val=c.val*2^H+v.val := by change v.val+2^H*c.val=_;ring
    rw [ord]
    by_cases same : c=b
    · subst c;simp [hits]
    · have sep : c.val≠b.val:=fun he=>same (Fin.ext he)
      have no : ¬ hits (some (c,v)) b lo hi := by simp [hits,same]
      simp only [no,iff_false]
      rcases lt_or_gt_of_ne sep with left|right
      · have gap:=Nat.mul_le_mul_right (2^H) left
        rw [Nat.succ_mul] at gap
        have:=v.isLt;omega
      · have gap:=Nat.mul_le_mul_right (2^H) right
        rw [Nat.succ_mul] at gap
        omega

theorem prefix_difference (field : Fin n→Arrival B H) (b : Fin B) {lo hi : ℕ}
    (order : lo≤hi) (cap : hi≤2^H) :
    count (fun i=>(number (field i)).val<b.val*2^H+hi)=
      count (fun i=>(number (field i)).val<b.val*2^H+lo)+count (fun i=>hits (field i) b lo hi) := by
  simp only [count_eq_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←test (field i) b order cap]
  split_ifs <;> omega

/-- Actual fallback leaf words use the chosen book's complete address,
left-aligned at the common public maximum height. -/
def arrived (height_le : h≤H) (b : Fin B) (x : Bits h) : Arrival B H :=
  some (b,⟨start H x,by
    have pos:=Nat.two_pow_pos (H-h)
    have up : start H x<stop H x := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) pos
    exact up.trans_le (stop_le height_le x)⟩)

theorem geometry {h d : ℕ} (high : h≤H) (edge : d≤h) (b : Fin B) (x : Bits h) (v : Bits d) :
    hits (arrived high b x) b (start H v) (stop H v) ↔ cut edge x=v := by
  simpa [arrived,hits] using member edge high x v

/-- Low and high words are two actual entries of the exclusive prefix produced by the same native histogram. -/
theorem run_read (base : ℕ) (key : Expr) (field : Fin n→Arrival B H) (m : Memory w)
    (valid : ∀i,key.eval m (i.val:Word w)=((number (field i)).val:Word w))
    (fits : key.Fits w base) (room : Histogram.stop base n (B*2^H+1)<2^w) :
    let tag:=fun i=>number (field i)
    let mem:=Histogram.after base key tag m
    (Histogram.program w base n (B*2^H+1) key).Exec m mem (Histogram.ticks n (B*2^H+1) key) ∧
      ∀ (b : Fin B) (lo hi : ℕ),lo≤hi → hi≤2^H →
        mem (Histogram.starts base n (B*2^H+1)+(b.val*2^H+hi))-
        mem (Histogram.starts base n (B*2^H+1)+(b.val*2^H+lo))=(count (fun i=>hits (field i) b lo hi):Word w) := by
  dsimp only
  refine ⟨Histogram.run base key _ m valid fits room,?_⟩
  intro b lo hi order cap
  have total:=Nat.mul_le_mul_right (2^H) b.isLt
  rw [Nat.succ_mul] at total
  rw [Histogram.prefix_read _ _ _ _ _ (by omega),Histogram.prefix_read _ _ _ _ _ (by omega)]
  rw [prefix_difference field b order cap,Nat.cast_add]
  exact add_sub_cancel_left _ _

end
end Hierarchy.DescentPrivateLeafHistogram

end OAI
