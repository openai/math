import OAI.Computability.NearSquareRoot.InterchangeROMOuterNative
import OAI.Computability.NearSquareRoot.InterchangeROMBankCompose

/-! # Unbanking the selected main-field swap on native center values -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMExpose
  NearSquareRoot.InterchangeSpectralFibre

/-- Each genuine digit recovers its row in the bank. Swapping the main fields
inside that row preserves both of its prefix coordinates. -/
theorem gather_main {b a m W : ℕ} (q : Request b) (hb : 2 ≤ b)
    (hn : 0 < a+m+a) (hw : a+m+a < q.width) (ok : q.Admissible) (hW : 0 < W) :
    let i := InterchangeROMStars.frame a m q hb hn hw ok
    BatchFrame.gather (axisP i) (axisG i) (axisB i) (axisF i) hW
      (fun u _ => paddedRow i u ∘ swapMain (OuterReserves.main a m)) () =
      centerValues i ∘ swapMain (OuterReserves.main a m) := by
  intro i
  funext k
  simp only [BatchFrame.gather,paddedRow,BatchFrame.padded,Function.comp_apply,swapMain,
    Equiv.symm_apply_apply,BatchRows.select_row_group]
  change centerValues i _ = centerValues i (swapMain _ k)
  apply congrArg (centerValues i)
  apply Prod.ext
  · exact (BatchFrame.prefixView (axisP i ()) i.b).cast.apply_symm_apply k.1
  · rfl

private theorem swap_count {m b f : ℕ} {P G B : Dims.Tape} {J : Type} [DecidableEq J]
    (slot : Fin m ↪ J) (rows : Series (Loom.Keys P G B J (Adic.Block b f))) (v) :
    (stripe rows (v ∘ swapMain slot)).count = (stripe rows v).count := by
  let σ := swapMain slot (P := P) (G := G) (B := B) (b := b) (f := f)
  have inv : Function.Involutive σ := by
    rintro ⟨p,u,g,w,s⟩
    simp only [σ,swapMain,Prod.mk.injEq,true_and,and_true]
    constructor <;> funext j <;> by_cases h : j ∈ Set.range slot <;> simp [h]
  exact Controlled.stripe_count_perm rows ⟨σ,σ,inv,inv⟩ v

theorem after_main_count {b a m : ℕ} (q : Request b) (hb : 2 ≤ b)
    (hn : 0 < a+m+a) (hw : a+m+a < q.width) (ok : q.Admissible) :
    (InterchangeROMStars.afterMain a m q hb hn hw ok).count = q.payload.count := by
  let i := InterchangeROMStars.frame a m q hb hn hw ok
  exact (swap_count (OuterReserves.main a m) (centerRows i) (centerValues i)).trans (data_counts i).2.2.2.2.1

theorem stream_main_count {b a m : ℕ} (q : Request b) (hb : 2 ≤ b)
    (hn : 0 < a+m+a) (hw : a+m+a < q.width) (ok : q.Admissible) (W : ℕ) :
    let i := InterchangeROMStars.frame a m q hb hn hw ok
    (stream i W (swapMain (OuterReserves.main a m))).count = (stream i W id).count := by
  intro i
  let v := fun u : Fin W => stripe (groupedRows i W) (paddedRow i u ∘ swapMain (OuterReserves.main a m))
  let w := fun u : Fin W => stripe (groupedRows i W) (paddedRow i u)
  have h (u : Fin W) : (v u).count = (w u).count :=
    swap_count (OuterReserves.main a m) (groupedRows i W) (paddedRow i u)
  change (stripe (Series.natural W) v).count = (stripe (Series.natural W) w).count
  apply Nat.le_antisymm
  · simpa only [Nat.one_mul] using InterchangeROMBank.stripe_counts_le (Series.natural W) v w
      (by decide : 0 < 1) (fun u => (h u).le.trans_eq (Nat.one_mul _).symm)
  · simpa only [Nat.one_mul] using InterchangeROMBank.stripe_counts_le (Series.natural W) w v
      (by decide : 0 < 1) (fun u => (h u).ge.trans_eq (Nat.one_mul _).symm)

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
