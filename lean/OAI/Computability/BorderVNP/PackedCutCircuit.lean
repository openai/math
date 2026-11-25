import OAI.Computability.BorderVNP.PackedWordCircuit
import OAI.Computability.BorderVNP.ShortenSeedDescriptor

/-! # Boolean execution of the public interval split

Each sorted cable row and each constant-numbered pool determines a cut descriptor. The Boolean
circuit here produces the actual old bit offset, selected width and new terminal offset of the
network in `ShortenSeedDescriptor`. All rows share the previous sorting and prefix-scan gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CutCircuit

open VPVNP.VerifierNetwork Word ParseBatchSort Shortening.SeedIntervals

/-- Four word operands after the sorting and bin-prefix scans. -/
inductive Input where | start | width | lo | hi
  deriving DecidableEq

instance : Fintype Input :=
  ⟨{.start, .width, .lo, .hi}, by intro i; cases i <;> simp⟩

/-- Three quantities needed at each endpoint when writing the sparse terminal plan. -/
inductive Result where | start | span | ordinal
  deriving DecidableEq

instance : Fintype Result :=
  ⟨{.start, .span, .ordinal}, by intro i; cases i <;> simp⟩

/-- Public input words of the actual split-network descriptor. -/
def Input.read (d : CutDescriptor) : Input → ℕ
  | .start => d.start | .width => d.width | .lo => d.lo | .hi => d.hi

/-- The actual start, width and terminal ordinal used by the chosen band. -/
def Result.read (d : CutDescriptor) : Result → ℕ
  | .start => d.localStart | .span => d.span | .ordinal => d.ordinal

private def offset (side : Input) : WidthExpr Input :=
  .binary .minimum (.field .width) (.binary .sub (.field side) (.field .start))

private def expression : Result → WidthExpr Input
  | .start => offset .lo
  | .span => .binary .sub (offset .hi) (offset .lo)
  | .ordinal => .binary .sub (.binary .add (.field .start) (offset .lo)) (.field .lo)

private theorem exact_eval (d : CutDescriptor) (r : Result) :
    (expression r).eval (Input.read d) = r.read d := by cases r <;> rfl

private theorem safe {d : CutDescriptor} {w : ℕ} (hroom : d.start + d.width < 2^w)
    (hlo : d.lo < 2^w) (hhi : d.hi < 2^w) (r : Result) :
    (expression r).Fits w (Input.read d) := by
  cases r <;> simp only [expression, offset, WidthExpr.Fits, WidthExpr.eval, Op.apply, Input.read] <;> omega

private theorem nodes (r : Result) : (expression r).nodes ≤ 11 := by cases r <;> decide

/-- Actual batched descriptor circuit. Sorting and group prefix computation can be spliced
once as `source`, independently of the number of bands read. -/
theorem exists_local_cutFrame {σ Row : Type*} [Fintype σ] [Fintype Row] (w : ℕ)
    (source : Frame σ (Row × Input × Fin w)) :
    ∃ out : Frame σ (Row × Result × Fin w),
      out.size ≤ source.size + 1 + Fintype.card Row * (3300 * (w+1)^2) ∧
      ∀ (x : σ → Bool) (i : Row) (d : CutDescriptor),
        (∀ f, value (fun j => source.eval x (i,f,j)) = f.read d) →
        d.start + d.width < 2^w → d.lo < 2^w → d.hi < 2^w →
        ∀ r, value (fun j => out.eval x (i,r,j)) = r.read d := by
  classical
  let leaf (i : Row × Result) : Frame (Row × Input × Fin w) (Fin w) :=
    ((expression i.2).frame w).subst (Frame.initial (fun f => (i.1,f)))
  obtain ⟨joint, hj, he⟩ := Crossing.exists_parallelFrames leaf
  let names (z : Row × Result × Fin w) : Σ _ : Row × Result, Fin w := ⟨(z.1,z.2.1),z.2.2⟩
  refine ⟨(joint.select names).subst source, ?_, ?_⟩
  · have hl (i : Row × Result) : (leaf i).size ≤ 1100 * (w+1)^2 := by
      simp only [leaf, Frame.subst_size, Frame.initial_size, zero_add]
      exact ((expression i.2).frame_size w).trans (by
        have hn := Nat.mul_le_mul_right (100 * (w+1)^2) (nodes i.2)
        simpa only [← Nat.mul_assoc] using hn)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    have hcard : Fintype.card Result = 3 := by decide
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, hcard, nsmul_eq_mul] at hsum
    rw [Frame.subst_size, Frame.select_size]
    calc
      _ ≤ source.size + (1 + (Fintype.card Row * 3) * (1100 * (w+1)^2)) :=
        Nat.add_le_add_left (hj.trans (Nat.add_le_add_left hsum 1)) _
      _ = _ := by ring
  · intro x i d hinput hroom hlo hhi r
    let z := fun p : Input × Fin w => source.eval x (i,p)
    have hzin : (fun f => value (fun j => z (f,j))) = Input.read d := funext hinput
    have hfit : (expression r).Fits w (fun f => value (fun j => z (f,j))) := by
      rw [hzin]
      exact safe hroom hlo hhi r
    calc
      _ = value (fun j => ((expression r).frame w).eval z j) := by
        apply congrArg value
        funext j
        simp only [Frame.subst_eval, Frame.select_eval, names, he, leaf]
        congr 1
        funext p
        simp [z]
      _ = (expression r).eval (fun f => value (fun j => z (f,j))) :=
        (expression r).frame_value w z hfit
      _ = r.read d := by rw [hzin, exact_eval]

/-- Actual batched descriptor circuit. Sorting and group prefix computation can be spliced
once as `source`, independently of the number of bands read. -/
theorem exists_cutFrame {σ Row : Type*} [Fintype σ] [Fintype Row] (w : ℕ)
    (source : Frame σ (Row × Input × Fin w)) :
    ∃ out : Frame σ (Row × Result × Fin w),
      out.size ≤ source.size + 1 + Fintype.card Row * (3300 * (w+1)^2) ∧
      ∀ (x : σ → Bool) (d : Row → CutDescriptor),
        (∀ i f, value (fun j => source.eval x (i,f,j)) = f.read (d i)) →
        (∀ i, (d i).start + (d i).width < 2^w ∧ (d i).lo < 2^w ∧ (d i).hi < 2^w) →
        ∀ i r, value (fun j => out.eval x (i,r,j)) = r.read (d i) := by
  obtain ⟨f,hf,he⟩ := exists_local_cutFrame w source
  exact ⟨f,hf,fun x d h fit i => he x i (d i) (h i) (fit i).1 (fit i).2.1 (fit i).2.2⟩

end Packing.CutCircuit

end BorderVNP
end Computability
end OAI
