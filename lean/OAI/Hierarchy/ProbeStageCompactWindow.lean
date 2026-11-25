import OAI.Hierarchy.ProbeStagePhysicalOrdinal
import OAI.Hierarchy.ProbeStageVisitFrame

namespace OAI
/-! # Fixed allocator row at the bottom of the original zero group bank -/

namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

def base (h : ℕ) := 2^h
def row (h : ℕ) : Record.Row :=
  ⟨base h+0,base h+1,base h+2,base h+3,base h+4,base h+5⟩

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))

/-- The three original output words are installed when the counted visit
returns. Every other external cell outside the eight-word window agrees
throughout the two actual computations. -/
def Common (x : ℕ) : Prop :=
  (x<base h ∨ base h+8≤x) ∧ ∀ k : Fin 3,x≠rankAddr h d j k i

/-- The staged run holds the same three mutable output values at fixed
addresses. The other five window words hold the input IDs and loop bounds. -/
structure Model (saved : Fin 8→Word (ramWidth h d)) (m n : Memory (ramWidth h d)) : Prop where
  common : ∀ x,Common j i x→n x=m x
  result : ∀ k : Fin 3,n (base h+3+k.val)=m (rankAddr h d j k i)
  fixed : ∀ k : Fin 8,k.val<3 ∨ 6≤k.val → n (base h+k.val)=saved k

theorem window_before (hh : 4≤h) (t : ℕ) : base h+8≤phase h d copies t := by
  have small : 8≤2^h := (show 8≤2^4 by decide).trans (Nat.pow_le_pow_right (by decide) hh)
  have cap := height_extent h d
  have scaled := Nat.mul_le_mul_right (extent h d) (Nat.le_add_right 3 (t*stride d copies))
  unfold phase base
  omega

theorem cell_low (x : Cell h d) : phase h d copies j≤x.addr j := by
  cases x <;> simp only [Cell.addr,rankAddr,scratch,region,bankBase] <;> omega

theorem common_temp (hh : 4≤h) (k : Fin 12) : Common j i (scratch h d j k) := by
  refine ⟨Or.inr ((window_before (d:=d) hh j).trans (cell_low j (.temp k))),?_⟩
  exact fun t => (rank_scratch h d j t i k).ne'

theorem common_area (hh : 4≤h) (k : Fin 16) (off : Fin (regionSize h d)) :
    Common j i (region h d j k+off.val) := by
  refine ⟨Or.inr ((window_before (d:=d) hh j).trans (cell_low j (.area k off))),?_⟩
  intro t eqn
  have bad : (Cell.area k off : Cell h d)=.rank t i := cell_injective h d j eqn
  cases bad

theorem common_arg (hh : 4≤h) (k : Fin 3) : Common j i (argumentAddr j i k) := by
  refine ⟨Or.inr ?_,?_⟩
  · have low:=window_before (d:=d) hh j
    change _≤allocatorBase h d copies j+_*_+_
    unfold allocatorBase bankBase
    omega
  · intro t eqn
    exact mayWrite_not_argument (d:=d) (j:=j.val) i i k (Or.inl ⟨t,eqn⟩)

namespace Model
variable {j i} {saved : Fin 8→Word (ramWidth h d)} {m n : Memory (ramWidth h d)}

/-- Native writes to the same shared location preserve the transported row. -/
theorem update_common (s : Model j i saved m n) {x : ℕ} (loc : Common j i x) (v : Word (ramWidth h d)) :
    Model j i saved (Function.update m x v) (Function.update n x v) := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    by_cases eqn : a=x
    · simp [eqn]
    · simpa only [Function.update_of_ne eqn] using s.common a ha
  · intro k
    have diff : base h+3+k.val≠x := by have cut:=loc.1;omega
    simpa only [Function.update_of_ne diff,Function.update_of_ne (loc.2 k).symm] using s.result k
  · intro k keep
    have diff : base h+k.val≠x := by have cut:=loc.1;omega
    simpa only [Function.update_of_ne diff] using s.fixed k keep

/-- Writes to the original rank location are carried out at the corresponding
fixed staging address until the final three physical stores. -/
theorem update_result (s : Model j i saved m n) (k : Fin 3) (v : Word (ramWidth h d)) :
    Model j i saved (Function.update m (rankAddr h d j k i) v) (Function.update n (base h+3+k.val) v) := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    have diff : a≠base h+3+k.val := by have cut:=ha.1;omega
    simpa only [Function.update_of_ne diff,Function.update_of_ne (ha.2 k)] using s.common a ha
  · intro t
    by_cases eqn : t=k
    · simp [eqn]
    · have lo : base h+3+t.val≠base h+3+k.val := by
        intro same
        exact eqn (Fin.ext (Nat.add_left_cancel same))
      have hi : rankAddr h d j t i≠rankAddr h d j k i := by
        intro same
        have bad : (Cell.rank t i : Cell h d)=.rank k i := cell_injective h d j same
        exact eqn (Cell.rank.inj bad).1
      simpa only [Function.update_of_ne lo,Function.update_of_ne hi] using s.result t
  · intro t keep
    have diff : base h+t.val≠base h+3+k.val := by omega
    simpa only [Function.update_of_ne diff] using s.fixed t keep
end Model

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
