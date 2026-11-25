import OAI.Computability.NearSquareRoot.CRTPositionFourCommandLarge
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandRaw
import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowTotal

/-! # Arithmetic correctness of four position stages at every reserve width

The only geometric condition is the number of fixed endpoints. The arbitrary
clocks in this file need not be bounded by the fast permutation rate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Adic
open IntegerMultiplication.Loom NearSquareRoot.Space GeneratorSyntax CommonRegisters KernelEffectiveFamily
open ReserveStage PositionRows
noncomputable section

abbrev SomeTime {I : Type} (c : Cmd) (source output : I → Tree) :=
  ∃ t : I → ℕ, EffectiveTask.Runs c t source output

private theorem before {I : Type} {a b : Cmd} {x y z : I → Tree}
    (h : SomeTime a x y) (g : SomeTime b y z) : SomeTime (a.join b) x z := by
  obtain ⟨_,ha⟩ := h
  obtain ⟨_,hb⟩ := g
  exact ⟨_,ha.comp hb⟩

private theorem park {I : Type} {a : Cmd} {x y : I → Tree} (s : I → Tree)
    (h : SomeTime a x y) :
    SomeTime (rightCmd a) (fun i => .fork (s i) (x i)) (fun i => .fork (s i) (y i)) := by
  obtain ⟨t,ha⟩ := h
  exact ⟨fun i => (s i).count+t i, command_contract (rightCmd a) from (show Task t x y from ⟨a,ha⟩).right s⟩

private theorem stageRaw {I : Type} {k lo hi : I → ℕ} (s : (i : I) → ReserveStage (k i) (lo i) (hi i))
    {a b c : Cmd} {x y z w : I → Tree}
    (f : SomeTime a (fun i => .fork (swapKey (s i)) (x i)) y)
    (m : SomeTime b (fun i => .fork (middleKey (s i)) (y i)) z)
    (g : SomeTime c (fun i => .fork (swapKey (s i)) (z i)) w) :
    SomeTime (stageCmd a b c) (fun i => shell (s i) (x i)) w :=
  before (before (park _ (park _ f)) (park _ m)) g

private theorem underRaw {I : Type} {k lo hi : I → ℕ} (s : (i : I) → ReserveStage (k i) (lo i) (hi i))
    {c : Cmd} {x y : I → Tree} (h : SomeTime c x y) :
    SomeTime (underCmd c) (fun i => shell (s i) (x i)) (fun i => shell (s i) (y i)) :=
  park _ (park _ (park _ h))

private theorem fourRaw {I : Type} {k lo hi : I → ℕ} {c : Cmd}
    (s : (j : Fin 4) → (i : I) → ReserveStage (k i) (lo i) (hi i)) (v : Fin 5 → I → Tree)
    (h : ∀ j : Fin 4, SomeTime c (fun i => shell (s j i) (v j.castSucc i)) (v j.succ)) :
    SomeTime (fourCmd c) (fun i => fullShell (fun j => s j i) (v 0 i)) (v 4) :=
  before (before (before (underRaw (s 3) (underRaw (s 2) (underRaw (s 1) (h 0))))
    (underRaw (s 3) (underRaw (s 2) (h 1)))) (underRaw (s 3) (h 2))) (h 3)

abbrev MiddleTotal (cmd : Cmd) : Prop :=
  ∀ {I : Type} (k lo hi : I → ℕ) (fit : ∀ i, lo i+hi i ≤ k i)
    {U : I → Type} (u : (i : I) → Series (U i)) (_pos : ∀ i, 0<(u i).count)
    (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead),
    SomeTime cmd (fun i => .fork (send (tally (hi i),tally (k i-lo i-hi i),tally (lo i),Reflections.table (q i)))
      (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i a => f i (ReserveTile.lift (fit i) (flatBitPullback (q i)) a)))

private theorem read_append {k lo hi : ℕ} (l : List (ReserveStage k lo hi))
    (s : ReserveStage k lo hi) (m : ReserveStage k lo hi → Equiv.Perm (Block 2 k)) (a : Block 2 k) :
    flatReads (l++[s]) m a = flatReads l m (s.flatRead (m s) a) := by
  induction l with
  | nil => rfl
  | cons t l ih => exact congrArg (t.flatRead (m t)) ih

set_option maxHeartbeats 1000000 in
theorem reserve_raw {core : Cmd} (middle : MiddleTotal (RowCommand.command core))
    {I : Type} (k lo hi : I → ℕ) (cap : ∀ i,lo i+hi i ≤ k i/2-2)
    {U : I → Type} (u : (i : I) → Series (U i)) (pos : ∀ i,0<(u i).count)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead) :
    SomeTime (reserveCmd core) (fun i => .fork (send (tally (lo i),tally (hi i),Reflections.table (p i)))
      (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i a => f i (flatBitPullback (p i) a))) := by
  let W i := 5*(2^k i*(u i).count)
  let stages i := four (p i) (cap i)
  let s (j : Fin 4) i := ReserveProgram.atStage (p i) (cap i) j
  have fit i : lo i+hi i ≤ k i := by have := cap i; omega
  let m i (s : ReserveStage (k i) (lo i) (hi i)) := ReserveTile.lift (fit i) (flatBitPullback s.inner)
  let act i (n : ℕ) := flatReads ((stages i).take n) (m i)
  let current (j : Fin 5) i a := f i (act i j.val a)
  let file (j : Fin 5) := cloth (fun i => line 2 (k i)) u (current j)
  have wc (y : (i : I) → Block 2 (k i) → U i → Bead) i :
      (cloth (fun i => line 2 (k i)) u y i).count ≤ W i :=
    ReserveSmall.beadClothCap k (fun i => (u i).count) u y pos (fun _ => le_rfl) i
  let pick i : PreCase := ⟨k i,lo i,hi i,p i,cap i,W i,
    (Nat.le_mul_of_pos_right (2^k i) (pos i)).trans (Nat.le_mul_of_pos_left _ (by decide : 0<5)),
    file 0 i,wc _ i⟩
  have step (j : Fin 4) : SomeTime (stageCmd (swapCmd false) (RowCommand.command core) (swapCmd true))
      (fun i => shell (s j i) (file j.castSucc i)) (file j.succ) := by
    have h i := four_bounds (p i) (cap i) (s j i) (ReserveProgram.atStage_mem (p i) (cap i) j)
    have len i := (h i).1.trans (fit i)
    let y i := current j.castSucc i ∘ swapsFlat (s j i).moves
    let z i := y i ∘ m i (s j i)
    have forward := swap_runs false k W (fun i => (s j i).moves) (fun i => (h i).2.1) len
      (fun i a => strip (u i) (current j.castSucc i a)) (wc _)
    have back := swap_runs true k W (fun i => (s j i).moves) (fun i => (h i).2.1) len
      (fun i a => strip (u i) (z i a)) (wc _)
    apply stageRaw (s j) ⟨_,forward.withoutSpace⟩ (middle k lo hi fit u pos (fun i => (s j i).inner) y)
    refine ⟨_,back.withoutSpace.conform (fun _ => rfl) (fun _ => rfl) ?_⟩
    intro i
    apply congrArg (stripe (line 2 (k i)))
    funext a
    apply congrArg (strip (u i))
    apply congrArg (f i)
    change (act i j.val) ((s j i).flatRead (m i (s j i)) a) = flatReads ((stages i).take (j.val+1)) (m i) a
    rw [List.take_succ_eq_append_getElem (by simp [stages]), read_append]
    rfl
  obtain ⟨t,h⟩ := before (show SomeTime prepareCmd _ _ from ⟨_,(prepare_runs.on pick).withoutSpace⟩)
    (fourRaw s file step)
  refine ⟨t,h.conform (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro i
  change stripe _ (fun a => strip (u i) (f i (flatReads ((stages i).take 4) (m i) a))) = _
  have len : (stages i).length = 4 := length_four _ _
  rw [← len,List.take_length,show flatReads (stages i) (m i) = flatBitPullback (p i) from four_canonicalReads _ _]
  rfl

theorem large_raw_of_middle {core : Cmd} (middle : MiddleTotal (RowCommand.command core))
    (a b : ℕ) {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀i, 0<(u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead)
    (cap : ∀i, payloadBits a (k i)+payloadBits b (k i) ≤ k i/2-2) :
    SomeTime ((widthCmd a b).join (reserveCmd core))
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  let V i := 2^k i*(u i).count
  have pre := width_runs a b k V p (fun i => Nat.le_mul_of_pos_right _ (pos i))
    (cloth (fun i => line 2 (k i)) u f) 5 (ReserveSmall.beadClothCap k _ u f pos (fun _ => le_rfl))
  exact before ⟨_,pre.withoutSpace⟩ (reserve_raw middle k _ _ cap u pos p f)

/-- Numeric reserves may be too small for the fast clock while the same
emitted program still permutes every input record according to its table. -/
theorem large_raw_runs {core : Cmd} (grouped : RowCommand.RawGroupedRuns core)
    (a b : ℕ) {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀ i, 0<(u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead)
    (cap : ∀ i, payloadBits a (k i)+payloadBits b (k i) ≤ k i/2-2) :
    SomeTime ((widthCmd a b).join (reserveCmd core))
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  apply large_raw_of_middle _ a b k u pos p f cap
  intro J width low high fit W payload positive q data
  obtain ⟨t,s,h⟩ := RowCommand.rawTableMiddle core grouped width low high fit payload positive q data
  exact ⟨t,h.withoutSpace⟩

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
