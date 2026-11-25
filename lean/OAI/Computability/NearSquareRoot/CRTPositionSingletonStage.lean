import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.CRTPositionProgram
import OAI.Computability.NearSquareRoot.CRTPositionGuardRuler
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # Singleton position opcodes from a shared physical descriptor -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Staff IntegerMultiplication.Strip IntegerMultiplication.Loom
open IntegerMultiplication.Packed NearSquareRoot.Space PositionPreparation

noncomputable section

theorem tailPayload_has {I : Type} {R : Regime I} {q : I → Tally × Tally}
    (h : R.Has (fun i => tailSwap (q i))) : R.Has q := by
  have t : R.Has (fun i => (true,true,true,q i)) := h
  exact t.ez (Easy.snd.compose (Easy.snd.compose Easy.snd))

theorem highPayload_has {I : Type} {R : Regime I} {q : I → Tally × Tally}
    (h : R.Has (fun i => highCnot (q i))) : R.Has q := by
  have t : R.Has (fun i => (true,true,false,q i)) := h
  exact t.ez (Easy.snd.compose (Easy.snd.compose Easy.snd))

private theorem pairLengths {I : Type} {R : Regime I} {q : I → Tally × Tally} (hq : R.Has q) :
    Realizes R (fun i => (q i).1.length) ∧ Realizes R (fun i => (q i).2.length) := by
  change R.Has (fun i => tally (q i).1.length) ∧ R.Has (fun i => tally (q i).2.length)
  simp only [recover_tally]
  exact ⟨hq.ez Easy.fst,hq.ez Easy.snd⟩

/-- Push the two short absolute selectors from the common register descriptor.
The elementary bounded gate then runs in time linear in this packet. -/
theorem absoluteGateStage {I : Type} {R : Regime I} {l : I → ℕ} (k : I → ℕ)
    (hi lo : (i : I) → Fin (k i)) (ord : ∀ i, lo i < hi i)
    (hk : Realizes R k) (hh : Realizes R fun i => (hi i).val) (hl : Realizes R fun i => (lo i).val)
    (φ : Bool × Bool → Bool × Bool) (ρ : ℝ) (hρ : 0 ≤ ρ)
    {U : I → Type} (u : (i : I) → Series (U i)) (z : ∀ i, (u i).count ≤ l i)
    (f : (i : I) → Block 2 (k i) → U i → Bead) :
    let flat i := line 2 (k i)
    Breeze (Spindle.modes k (τ := ρ)) R (fun i => (flat i).count) l
      (together R.header (cloth flat u f))
      (cloth flat u fun i a => f i (flatGateAt (hi i) (lo i) (ord i) (digitGate φ) a)) := by
  intro flat
  let data := cloth flat u f
  let raw i := send (elementRulers k (fun i => (hi i).val) (fun i => (lo i).val) i)
  let V i := (Tree.fork (raw i) (data i)).count
  have st := terminal (by decide : 2 ≤ 2) k hk
  have alive := cloth_size flat u st f z
  have keys : R.Small raw := hk.pair (hh.pair hl)
  have input := (Drive.small st.1 alive keys).twice (Drive.self st.1 alive)
  obtain ⟨d,carry⟩ := input
  have run := flatGateCloth k V hi lo ord φ u f (fun i => by
    change (data i).count ≤ (raw i).count + (data i).count + 1
    omega)
  exact Breeze.launch ⟨d,carry.sequence (Sized.size_shield carry.out carry.budget run.forget)⟩
    (Spindle.belly k hρ)

private def tailPair {k G : ℕ} (q : Tally × Tally) (v : WellFormed k G (tailSwap q)) : Fin k × Fin k :=
  (⟨q.1.length,v.1⟩,⟨q.2.length,v.2.1⟩)

def tailBlock {k G : ℕ} (q : Tally × Tally) (v : WellFormed k G (tailSwap q)) : Block 2 k → Block 2 k :=
  swapFlat (tailPair q v)

theorem tailBlock_bits {k G : ℕ} (q : Tally × Tally) (v : WellFormed k G (tailSwap q))
    (y : Block 2 k) :
    prefixBit (tailBlock q v y) = act G (prefixBit y) (tailSwap q) := by
  funext j
  rw [tailBlock,swapFlat_prefixBit]
  simp only [act,swapPair,v.1,v.2.1,and_self,↓reduceDIte]
  rfl

theorem tailStage {I : Type} {R : Regime I} {l : I → ℕ} (k : I → ℕ) (q : I → Tally × Tally)
    (hk : Realizes R k) (hq : R.Has q) (G : I → ℕ) (v : ∀ i, WellFormed (k i) (G i) (tailSwap (q i)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) {U : I → Type} (u : (i:I) → Series (U i)) (z : ∀ i, (u i).count ≤ l i)
    (f : (i:I) → Block 2 (k i) → U i → Bead) :
    let flat i := line 2 (k i)
    Breeze (Spindle.modes k (τ := ρ)) R (fun i => (flat i).count) l
      (together R.header (cloth flat u f)) (cloth flat u (fun i y => f i (tailBlock (q i) (v i) y))) := by
  let p i := tailPair (q i) (v i)
  have ne i : (p i).1 ≠ (p i).2 := fun h => (v i).2.2.1 (congrArg Fin.val h)
  obtain ⟨a,b⟩ := pairLengths hq
  have top := b.select a (a.below b)
  have bottom := a.select b (a.below b)
  have H : Realizes R (fun i => (max (p i).1 (p i).2).val) := by
    convert top using 1
    funext i
    change max (q i).1.length (q i).2.length = _
    split <;> omega
  have L : Realizes R (fun i => (min (p i).1 (p i).2).val) := by
    convert bottom using 1
    funext i
    change min (q i).1.length (q i).2.length = _
    split <;> omega
  have run := absoluteGateStage k (fun i => max (p i).1 (p i).2) (fun i => min (p i).1 (p i).2)
    (fun i => min_lt_max.mpr (ne i)) hk H L Prod.swap ρ hρ u z f
  have eq i y : tailBlock (q i) (v i) y =
      flatGateAt (max (p i).1 (p i).2) (min (p i).1 (p i).2)
        (min_lt_max.mpr (ne i)) (digitGate Prod.swap) y := swapFlat_of_ne _ (ne i) _
  simpa only [eq] using run

private def chunkSlot {k : ℕ} (c : Fin 3) (j : Fin (k/3)) : Fin k :=
  (threeChunksWithTail k).symm (.inl (c,j))

private theorem highOrder {k : ℕ} (s d : Fin (k/3)) : chunkSlot 1 d < chunkSlot 2 s := by
  change d.val + k / 3 * 1 < s.val + k / 3 * 2
  omega

def highCnotBlock {k G : ℕ} (q : Tally × Tally) (v : WellFormed k G (highCnot q)) : Block 2 k → Block 2 k :=
  let s : Fin (k/3) := ⟨q.1.length,v.1⟩
  let d : Fin (k/3) := ⟨q.2.length,v.2⟩
  flatGateAt (chunkSlot 2 s) (chunkSlot 1 d) (highOrder s d) (digitGate (fun a => (a.1,xor a.2 a.1)))

theorem highCnotBlock_bits {k G : ℕ} (q : Tally × Tally) (v : WellFormed k G (highCnot q))
    (y : Block 2 k) :
    prefixBit (highCnotBlock q v y) = act G (prefixBit y) (highCnot q) := by
  let s : Fin (k/3) := ⟨q.1.length,v.1⟩
  let d : Fin (k/3) := ⟨q.2.length,v.2⟩
  have eq : highCnot (tally s.val,tally d.val) = highCnot q := by simp [s,d,recover_tally]
  funext j
  change prefixBit (flatGateAt (chunkSlot 2 s) (chunkSlot 1 d) _ _ y) j =
    passAction G (prefixBit y) (highCnot q) j
  rw [flatGateAt_xorLow,← eq,passAction_highCnot]
  obtain ⟨t,rfl⟩ := (threeChunksWithTail k).symm.surjective j
  rcases t with ⟨c,j⟩ | j
  · by_cases hc : c = 1
    · subst c
      by_cases hj : j = d <;> simp [gathered,chunkSlot,chunkWord,xorFrom,hj]
    · simp [gathered,chunkSlot,hc]
  · simp [gathered,chunkSlot]

theorem highCnotStage {I : Type} {R : Regime I} {l : I → ℕ} (k : I → ℕ) (q : I → Tally × Tally)
    (hk : Realizes R k) (hq : R.Has q) (G : I → ℕ) (v : ∀ i, WellFormed (k i) (G i) (highCnot (q i)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) {U : I → Type} (u : (i:I) → Series (U i)) (z : ∀ i, (u i).count ≤ l i)
    (f : (i:I) → Block 2 (k i) → U i → Bead) :
    let flat i := line 2 (k i)
    Breeze (Spindle.modes k (τ := ρ)) R (fun i => (flat i).count) l
      (together R.header (cloth flat u f)) (cloth flat u (fun i y => f i (highCnotBlock (q i) (v i) y))) := by
  let s i : Fin (k i/3) := ⟨(q i).1.length,(v i).1⟩
  let d i : Fin (k i/3) := ⟨(q i).2.length,(v i).2⟩
  obtain ⟨a,b⟩ := pairLengths hq
  have n := third_realizes hk
  have H : Realizes R (fun i => (chunkSlot 2 (s i)).val) := by
    simpa only [chunkSlot,threeChunksWithTail_bulk,s,Fin.val_two,mul_two,add_assoc] using (a.plus n).plus n
  have L : Realizes R (fun i => (chunkSlot 1 (d i)).val) := by
    simpa only [chunkSlot,threeChunksWithTail_bulk,d,Fin.val_one,mul_one] using b.plus n
  exact absoluteGateStage k (fun i => chunkSlot 2 (s i)) (fun i => chunkSlot 1 (d i))
    (fun i => highOrder (s i) (d i)) hk H L (fun a => (a.1,xor a.2 a.1)) ρ hρ u z f

end
end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
