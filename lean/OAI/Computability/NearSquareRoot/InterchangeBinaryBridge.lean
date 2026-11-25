import OAI.Computability.NearSquareRoot.CRTControlledXor
import OAI.Computability.IntegerMultiplication.Short

/-!
# Binary rectangular interchange from a fixed prime-radix interchange

P192's unary altitude program chooses the two padded field widths. Its halo
passes replicate whole records and keep each prefix, gap and suffix fixed.
The inverse halo recovers the genuine records after the native radix swap.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeBinary

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Loom IntegerMultiplication.Adic IntegerMultiplication.Code
  IntegerMultiplication.Spindle NearSquareRoot.Controlled

variable {I : Type} {r : Regime I} {b : ℕ} [NeZero b]

def radixWidth (hb : 2 ≤ b) (n : ℕ) := (altitude b hb (tally n)).length

private theorem width_bounds (hb : 2 ≤ b) (n : ℕ) :
    2^n ≤ b^(radixWidth hb n) ∧ b^(radixWidth hb n) ≤ b * 2^n ∧ radixWidth hb n ≤ n+1 := by
  simpa only [radixWidth, tally_length] using grows b hb (tally n)

theorem width_pos (hb : 2 ≤ b) (n : ℕ) : 0 < radixWidth hb n := by
  cases n with
  | zero => exact Nat.zero_lt_succ 0
  | succ n =>
    obtain ⟨h,_,_⟩ := width_bounds hb (n+1)
    by_contra! hx
    have hr : radixWidth hb (n+1) = 0 := by omega
    rw [hr,pow_zero,pow_succ] at h
    have := Nat.two_pow_pos n
    omega

theorem width_has (hb : 2 ≤ b) (n : I → ℕ) (hn : r.Has (tally ∘ n)) :
    r.Has (fun i => tally (radixWidth hb (n i))) := by
  simpa only [Function.comp_def, radixWidth, recover_tally] using hn.thenDo (altitude_poly b hb)

private theorem haloGap (hb : 2 ≤ b) (n : ℕ) : Gap (line 2 n) (line b (radixWidth hb n)) b := by
  obtain ⟨a,c,_⟩ := width_bounds hb n
  exact ⟨by simpa only [lineSize] using a,by simpa only [lineSize, Nat.mul_comm b] using c, by omega⟩

variable (P G B : I → Tape) (n : I → ℕ)

/-- Address of the original binary record to duplicate at a padded address. -/
noncomputable def binaryRecord (hb : 2 ≤ b) (i : I) :
    SpanKey (P i) (G i) (B i) (Block b (radixWidth hb (n i))) →
      SpanKey (P i) (G i) (B i) (Block 2 (n i)) :=
  fill_ (fun i => line 2 (n i)) (fun i => line b (radixWidth hb (n i))) b
    (fun i => haloGap hb (n i)) P G B i

theorem halo_parts (hb : 2 ≤ b) (hn : r.Has (tally ∘ n))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (L : I → ℕ)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → Tree) (hv : Manifest _ L v) :
    let S i := stock 2 (P i) (G i) (B i) (n i)
    let D i := stock b (P i) (G i) (B i) (radixWidth hb (n i))
    let x i := v i ∘ binaryRecord P G B n hb i
    let z i := x i ∘ swapper _ _ _
    (∀ i, 1 ≤ (S i).count) ∧ (∀ i, (D i).count ≤ b^2*(S i).count) ∧
    Drive r (fun i => (S i).count) L (stackRun S v) (stackRun D x) ∧
    Drive r (fun i => (D i).count) L (stackRun D z) (stackRun S fun i => v i ∘ swapper _ _ _) := by
  let e i := radixWidth hb (n i)
  let s i := line 2 (n i)
  let t i := line b (e i)
  let gap i := haloGap hb (n i)
  let S := star_ s P G B
  let D := star_ t P G B
  let N i := (S i).count
  let N' i := (D i).count
  let x i := v i ∘ binaryRecord P G B n hb i
  let x' (i : I) := x i ∘ swapper _ _ _
  have sst := terminal (p:=2) (by decide) n hn
  have tst := terminal hb e (width_has hb n hn)
  have pos : ∀ i, 1 ≤ N i := (hp.station.product (sst.product (hg.station.product (sst.product hs.station)))).1
  have growth : ∀ i, N' i ≤ b^2 * N i := all_counts s t b gap P G B
  have pre : Drive r N L (stackRun S v) (stackRun D x) :=
    addHalo s t b gap P G B sst tst hp.station hg.station hs.station v hv
  have post : Drive r N' L (stackRun D x') (stackRun S fun i => v i ∘ swapper _ _ _) := by
    have vx : Manifest _ L x' := hv.shift (fun i a => binaryRecord P G B n hb i (swapper _ _ _ a))
    have g := subHalo s t b gap P G B sst tst hp.station hg.station hs.station x' vx
    change Drive r N' L _ (stackRun S fun i a => v i (fill_ s t b gap P G B i
      (swapper _ _ _ (thicken s t b gap P G B i a)))) at g
    simp only [paid_] at g
    exact g
  exact ⟨pos,growth,pre,post⟩

theorem padded_price {α : ℝ} (hα : 0 ≤ α) (hb : 2 ≤ b) :
    ∃ K : ℕ, ∀ i, modes (τ:=α) (fun j => radixWidth hb (n j)) i ≤ K*modes (τ:=α) n i := by
  let e i := radixWidth hb (n i)
  obtain ⟨K,hK⟩ := exists_nat_ge ((2:ℝ)^α)
  refine ⟨K,fun i => ?_⟩
  have hm : e i + 1 ≤ 2*(n i+1) := by have := (width_bounds hb (n i)).2.2; dsimp [e]; omega
  have hc : ((e i+1:ℕ):ℝ) ≤ 2*((n i+1:ℕ):ℝ) := by exact_mod_cast hm
  calc
    _ ≤ (2*((n i+1:ℕ):ℝ)) ^ α := Real.rpow_le_rpow (by positivity) hc hα
    _ = (2:ℝ)^α * modes (τ:=α) n i := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by dsimp [modes]; positivity)

/-- Given a native radix program on padded records, obtain the binary one.
The payload trees are transported whole in both halo passes. -/
theorem transfer {α : ℝ} (hα : 0 ≤ α) (hb : 2 ≤ b) (hn : r.Has (tally ∘ n))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (L : I → ℕ)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → Tree) (hv : Manifest _ L v)
    (native : let e i := radixWidth hb (n i)
      let s i := stock b (P i) (G i) (B i) (e i)
      let x i := v i ∘ binaryRecord P G B n hb i
      Breeze (modes (τ:=α) e) r (fun i => (s i).count) L
        (together r.header (stackRun s x)) (stackRun s fun i => x i ∘ swapper _ _ _)) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    Breeze (modes (τ:=α) n) r (fun i => (s i).count) L
      (together r.header (stackRun s v)) (stackRun s fun i => v i ∘ swapper _ _ _) := by
  let e i := radixWidth hb (n i)
  let s i := line 2 (n i)
  let t i := line b (e i)
  let S := star_ s P G B
  let D := star_ t P G B
  let N i := (S i).count
  let x i := v i ∘ binaryRecord P G B n hb i
  let x' (i : I) := x i ∘ swapper _ _ _
  obtain ⟨pos,growth,pre,post⟩ := halo_parts P G B n hb hn hp hg hs L v hv
  obtain ⟨_,k,move⟩ := Strip.Breeze.factor native pos (b^2) growth
  have F := belly n hα
  obtain ⟨K,bound⟩ := padded_price n hα hb
  have native' : Breeze (modes (τ:=α) n) r N L (together r.header (stackRun D x)) (stackRun D x') := by
    refine ⟨F,k,move.times (fun i => one_le_mul_of_one_le_of_one_le (unit_mass pos _ _) (F i)) K ?_⟩
    intro i
    unfold runrate
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (bound i) (by unfold mass; positivity)
  exact Spindle.Breeze.pipe (Strip.Breeze.launch pre F) (Spindle.Breeze.pipe native'
    (Strip.Breeze.launch (Rip.factor post pos (b^2) growth) F) (Drive.fetch pos pre.idle))
    (Rip.split pre.again).1

/-- Native radix interface for a streamed payload of P192 beads. No payload
width is assumed recoverable from the regime header. -/
def RadixBeads (b : ℕ) (r : Regime I) (α : ℝ) : Prop :=
  ∀ (P G B : I → Tape) (e : I → ℕ), (∀ i, 0 < e i) → r.Has (tally ∘ e) →
    Told r P → Told r G → Told r B → (∀ i d, d ∈ P i ++ G i ++ B i → d ≤ b) →
    ∀ (L : I → ℕ) {T : I → Type} (t : (i : I) → Series (T i)), (∀ i, (t i).count ≤ L i) →
    ∀ v : (i : I) → SpanKey (P i) (G i) (B i) (Block b (e i)) → T i → Bead,
      let s i := stock b (P i) (G i) (B i) (e i)
      Breeze (modes (τ:=α) e) r (fun i => (s i).count) L (together r.header (cloth s t v))
        (cloth s t fun i => v i ∘ swapper _ _ _)

/-- A prime-radix procedure over beads gives the exact rectangular interface
used by the controlled CRT and packed-bit permutation programs. -/
theorem rect_of_radix {α : ℝ} (hα : 0 ≤ α) (hb : 2 ≤ b) (size : Net.Shuttle.base ≤ b)
    (native : RadixBeads b r α) : RectInterchange r n α := by
  intro P G B hn hp hg hs bound L T t ht v
  have manifest := visible (l:=L) t v ht
  apply transfer P G B n hα hb hn hp hg hs L (fun i a => strip (t i) (v i a)) manifest
  exact native P G B (fun i => radixWidth hb (n i)) (fun i => width_pos hb (n i)) (width_has hb n hn)
    hp hg hs (fun i d hd => (bound i d hd).trans size) L t ht
    (fun i a => v i (binaryRecord P G B n hb i a))

/-- A uniform-length binary record is sent exactly as its list of bits. The
physical bits agree with the bead codec even when the record width is zero. -/
theorem bitstrings {α : ℝ} (rect : RectInterchange r n α)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (guard : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ Net.Shuttle.base)
    (L width : I → ℕ) (bound : ∀ i, width i ≤ L i)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → List Bool)
    (exactWidth : ∀ i x, (v i x).length = width i) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    Breeze (modes n (τ:=α)) r (fun i => (s i).count) L
      (together r.header (stackRun s fun i x => send (v i x)))
      (stackRun s fun i x => send (v i (swapper _ _ _ x))) := by
  let t i := Series.natural (width i)
  let value i a := notify.symm ∘ (t i).untab (v i a) (by simp [t,exactWidth])
  have run := rect P G B hn hp hg hs guard L t (fun i => by simpa [t] using bound i) value
  have repr (i : I) (a) : strip (t i) (value i a) = send (v i a) := by
    have bits : (fun d => send (value i a d)) =
        fun d => send ((t i).untab (v i a) (by simp [t,exactWidth]) d) := by
      funext d
      change Tree.atom (notify (notify.symm _)) = Tree.atom _
      rw [Equiv.apply_symm_apply]
    rw [strip,bits,stripe_eq',Series.recover]
  unfold cloth at run
  simp_rw [repr] at run
  exact run

end InterchangeBinary

end NearSquareRoot
end Computability
end OAI
