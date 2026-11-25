import OAI.Computability.NearSquareRoot.CRTControlledReserveRun
import OAI.Computability.NearSquareRoot.CRTControlledReserveIndex

/-! # Four bounded matching passes from the original position table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveStage
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Space

noncomputable section

private theorem flatReads_snoc {k lo hi : ℕ} (l : List (ReserveStage k lo hi))
    (s : ReserveStage k lo hi) (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k))
    (x : Block 2 k) :
    flatReads (l++[s]) m x = flatReads l m (s.flatRead (m s) x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a.flatRead (m a) (flatReads (l++[s]) m x) =
      a.flatRead (m a) (flatReads l m (s.flatRead (m s) x))
    rw [ih]

/-- A bounded pass on the middle field, with fixed high and low address bits.
The representation predicate can specify uniform payload widths for every row.
The involution table is read from the original regime header. -/
abbrev MiddlePass {I : Type} (r : Regime I) (k lo hi V T : I → ℕ)
    (fit : ∀ i, lo i+hi i ≤ k i) (C : (i : I) → (Block 2 (k i) → Tree) → Prop) : Prop :=
  ∀ (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i))),
    (∀ i, Function.Involutive (q i)) → (r.Has fun i => Reflections.table (q i)) →
    ∀ (g : (i : I) → Block 2 (k i) → Tree), (∀ i, C i (g i)) →
    (∀ i, (stripe (line 2 (k i)) (g i)).count ≤ V i) →
    BoundedTask T V (fun i => .fork (r.header i) (stripe (line 2 (k i)) (g i)))
      (fun i => stripe (line 2 (k i)) (g i ∘ ReserveTile.lift (fit i) (flatBitPullback (q i))))

private theorem widthOfTable {I : Type} {r : Regime I} {k : I → ℕ}
    (p : (i : I) → Equiv.Perm (Fin (k i))) (tab : r.Has fun i => Reflections.table (p i)) :
    r.Has (fun i => tally (k i)) := by
  have h := tab.ez (Easy.ruler Easy.identity)
  have eq i : ruler (Reflections.table (p i)) = tally (k i) := by
    rw [← recover_tally (ruler _),ruler_length]
    simp [Reflections.table]
  simpa only [id_eq,eq] using h

/-- Compile an arbitrary permutation and execute all four physical stages.
The middle routine receives its image table from the same regime header and
acts on the address field lying between the two reserved ends. -/
theorem boundedFourRunPrepared {I : Type} {r : Regime I} (k lo hi V T : I → ℕ)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (cap : ∀ i, lo i+hi i ≤ k i/2-2)
    (f : (i : I) → Block 2 (k i) → Tree)
    (C : (i : I) → (Block 2 (k i) → Tree) → Prop) (valid : ∀ i, C i (f i))
    (reindex : ∀ i g (e : Equiv.Perm (Block 2 (k i))), C i g → C i (g ∘ e))
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i)
    (width : r.Has fun i => tally (k i))
    (all : r.Has fun i => (four (p i) (cap i)).map ReserveProgram.encode)
    (middle : MiddlePass r k lo hi V T (fun i => by have := cap i; omega) C) :
    BoundedTask (fun i => (lo i+hi i+1)*V i+T i) V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) := by
  let stages i := four (p i) (cap i)
  let s (j : Fin 4) i := ReserveProgram.atStage (p i) (cap i) j
  let m i (a : ReserveStage (k i) (lo i) (hi i)) :=
    ReserveTile.lift (by have := cap i; omega : lo i+hi i ≤ k i) (flatBitPullback a.inner)
  let act i (n : ℕ) := flatReads ((stages i).take n) (m i)
  let current i (n : ℕ) := f i ∘ act i n
  let data i (n : ℕ) := stripe (line 2 (k i)) (current i n)
  let time i := (lo i+hi i+1)*V i+T i
  have sz i n : (data i n).count ≤ V i := by
    simpa only [data,current,stripe_count_perm] using inputCap i
  have room i : V i ≤ time i :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < lo i+hi i+1)).trans (Nat.le_add_right ..)
  have area i : 2^(k i) ≤ V i := by
    have h := inputCap i
    rw [stripe, Task.forest_count, Series.card, lineSize] at h
    omega
  have head := Regime.self.cooked (ripeOfWidth scale area)
  have run (j : Fin 4) : BoundedTask time V (fun i => .fork (r.header i) (data i j.val))
      (fun i => data i (j.val+1)) := by
    have limits i := four_bounds (p i) (cap i) (s j i) (ReserveProgram.atStage_mem (p i) (cap i) j)
    have desc := ReserveProgram.atStage_uniform p cap all j
    let input i := current i j.val ∘ swapsFlat (s j i).moves
    have ok i : C i (input i) := reindex i _ _ (reindex i _ _ (valid i))
    have step := boundedRunUniform k lo hi V T (s j) (fun i => (limits i).2.1) 1
      (fun i => by have := (limits i).1; have := cap i; omega) (fun i => current i j.val)
      (fun i => sz i j.val) scale width desc r.header Regime.self (fun i => m i (s j i))
      (middle (fun i => (s j i).inner) (fun i => (limits i).2.2) (desc.ez Easy.snd) input ok
        (fun i => by simpa only [input,stripe_count_perm] using sz i j.val))
    have charge i : ((s j i).moves.length+1)*V i+T i ≤ time i :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.succ_le_succ (limits i).1)) _
    apply (step.mono charge (fun _ => le_rfl)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro i
    apply congrArg (stripe (line 2 (k i)))
    funext x
    apply congrArg (f i)
    change _ = flatReads ((stages i).take (j.val+1)) (m i) x
    rw [List.take_succ_eq_append_getElem (by simp [stages]), flatReads_snoc]
    rfl
  have saved (j : Fin 4) := retainBoundedHeader (run j) head
    (show Volume (fun i => (V i : ℝ)) (fun i => data i j.val) from
      ⟨1,fun i => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr (sz i j.val)⟩) room
  have go := (((saved 0).compose (saved 1)).compose (saved 2)).compose (run 3)
  apply (go.bound (time' := time) (space' := V) 4 1 (fun i => by omega) (fun i => by simp)).conform
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro i
  change stripe _ (f i ∘ flatReads ((stages i).take 4) (m i)) = _
  have len : (stages i).length = 4 := length_four _ _
  rw [← len, List.take_length, show flatReads (stages i) (m i) = flatBitPullback (p i) from
    four_canonicalReads _ _]

/-- Prepare the four descriptors from a supplied permutation table and reserve widths. -/
theorem boundedFourRun {I : Type} {r : Regime I} (k lo hi V T : I → ℕ)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (cap : ∀ i, lo i+hi i ≤ k i/2-2)
    (f : (i : I) → Block 2 (k i) → Tree)
    (C : (i : I) → (Block 2 (k i) → Tree) → Prop) (valid : ∀ i, C i (f i))
    (reindex : ∀ i g (e : Equiv.Perm (Block 2 (k i))), C i g → C i (g ∘ e))
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i)
    (low : r.Has (fun i => tally (lo i))) (high : r.Has (fun i => tally (hi i)))
    (tab : r.Has fun i => Reflections.table (p i))
    (middle : MiddlePass r k lo hi V T (fun i => by have := cap i; omega) C) :
    BoundedTask (fun i => (lo i+hi i+1)*V i+T i) V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) :=
  boundedFourRunPrepared k lo hi V T p cap f C valid reindex inputCap scale (widthOfTable p tab)
    (ReserveProgram.compiler_uniform k lo hi p cap low high tab) middle

/-- With logarithmic end widths the table alone supplies every descriptor. -/
theorem boundedFourFromTable {I : Type} {r : Regime I} (a b : ℕ) (k V T : I → ℕ)
    (p : (i : I) → Equiv.Perm (Fin (k i)))
    (cap : ∀ i, payloadBits a (k i)+payloadBits b (k i) ≤ k i/2-2)
    (f : (i : I) → Block 2 (k i) → Tree)
    (C : (i : I) → (Block 2 (k i) → Tree) → Prop) (valid : ∀ i, C i (f i))
    (reindex : ∀ i g (e : Equiv.Perm (Block 2 (k i))), C i g → C i (g ∘ e))
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i) (tab : r.Has fun i => Reflections.table (p i))
    (middle : MiddlePass r k (fun i => payloadBits a (k i)) (fun i => payloadBits b (k i))
      V T (fun i => by have := cap i; omega) C) :
    BoundedTask (fun i => (payloadBits a (k i)+payloadBits b (k i)+1)*V i+T i) V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) :=
  boundedFourRunPrepared k _ _ V T p cap f C valid reindex inputCap scale (widthOfTable p tab)
    (ReserveProgram.table_uniform a b p cap tab) middle

/-- Execute the same four stages on a cloth of fixed-width records. Every
invocation of the middle program receives the original payload series. -/
theorem boundedFourCloth {I X : Type} [Codec X] {U : I → Type} {r : Regime I}
    (a b : ℕ) (k V T : I → ℕ) (u : (i : I) → Series (U i))
    (p : (i : I) → Equiv.Perm (Fin (k i)))
    (cap : ∀ i, payloadBits a (k i)+payloadBits b (k i) ≤ k i/2-2)
    (x : (i : I) → Block 2 (k i) → U i → X)
    (inputCap : ∀ i, (Loom.cloth (fun i => line 2 (k i)) u x i).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i) (tab : r.Has fun i => Reflections.table (p i))
    (middle : ∀ (q : (i : I) → Equiv.Perm
        (Fin (k i-payloadBits a (k i)-payloadBits b (k i)))),
      (∀ i, Function.Involutive (q i)) → (r.Has fun i => Reflections.table (q i)) →
      ∀ (y : (i : I) → Block 2 (k i) → U i → X),
      (∀ i, (Loom.cloth (fun i => line 2 (k i)) u y i).count ≤ V i) →
      BoundedTask T V (fun i => .fork (r.header i) (Loom.cloth (fun i => line 2 (k i)) u y i))
        (Loom.cloth (fun i => line 2 (k i)) u (fun i z =>
          y i ((ReserveTile.lift (by have := cap i; omega) (flatBitPullback (q i))) z)))) :
    BoundedTask (fun i => (payloadBits a (k i)+payloadBits b (k i)+1)*V i+T i) V
      (fun i => .fork (r.header i) (Loom.cloth (fun i => line 2 (k i)) u x i))
      (Loom.cloth (fun i => line 2 (k i)) u (fun i z => x i (flatBitPullback (p i) z))) := by
  let C i (g : Block 2 (k i) → Tree) := ∃ y : Block 2 (k i) → U i → X,
    g = fun z => Loom.strip (u i) (y z)
  refine boundedFourFromTable a b k V T p cap (fun i z => Loom.strip (u i) (x i z)) C
    (fun i => ⟨x i,rfl⟩) ?_ inputCap scale tab ?_
  · intro i g e h
    obtain ⟨y,rfl⟩ := h
    exact ⟨y ∘ e,rfl⟩
  · intro q inv has g valid bound
    choose y hy using valid
    have eq : g = fun i z => Loom.strip (u i) (y i z) := funext hy
    subst g
    exact middle q inv has y bound

end
end Controlled.ReserveStage

end NearSquareRoot
end Computability
end OAI
