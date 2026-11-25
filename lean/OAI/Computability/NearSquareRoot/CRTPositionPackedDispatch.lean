import OAI.Computability.NearSquareRoot.CRTPositionChunkView
import OAI.Computability.NearSquareRoot.CRTPositionGuardRuler
import OAI.Computability.NearSquareRoot.CRTPositionProgramStream
import OAI.Computability.NearSquareRoot.CRTPositionProgramPassAction
import OAI.Computability.NearSquareRoot.InterchangeRectangular

/-! # P192 dispatch of a packed position opcode on a native binary word

The high remainder stays in its original place. The three complete native chunks
use the full read table and residue from the opcode. On an empty pass the finite
P192 program branches before invoking rectangular interchange.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Staff
open IntegerMultiplication.Strip IntegerMultiplication.Loom IntegerMultiplication.Packed
open PositionPreparation

noncomputable section

def packedRead {n : ℕ} (t : List Tally) (j : Fin n) : Option (Fin n) :=
  let v := (Iter.pick (tally n) (t,tally j.val)).length
  if h : v < n then some ⟨v,h⟩ else none

theorem packedRead_codes {n : ℕ} (read : Fin n → Option (Fin n)) (j : Fin n) :
    packedRead (List.ofFn fun a => tally (((read a).map Fin.val).getD n)) j = read j := by
  simp only [packedRead,Iter.pick,tally_length,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
    dite_eq_left j.isLt,Option.getD_some]
  have recover (v : Option (Fin n)) :
      (if h : (v.map Fin.val).getD n < n then some (⟨(v.map Fin.val).getD n,h⟩ : Fin n) else none) = v := by
    cases v with
    | none => simp
    | some a => simp [a.isLt]
  exact recover (read j)

theorem packedRead_table {k G : ℕ} {q : Tally × List Tally} (h : WellFormed k G (packed q)) :
    List.ofFn (fun j : Fin (k/3) => tally (((packedRead q.2 j).map Fin.val).getD (k/3))) = q.2 := by
  obtain ⟨r,t⟩ := q
  obtain ⟨_,read,rfl⟩ := h
  simp only [packedRead_codes]

theorem passAction_packedRead {k G : ℕ} (q : Tally × List Tally) (w : Fin k → Bool) :
    passAction G w (packed q) =
      gathered (fun j => if residuePass G j = q.1.length then packedRead q.2 j else none) w := rfl

private theorem posGuard (k : ℕ) : 0 < guardWidth k := by unfold guardWidth; omega

def packedPass {k : ℕ} (q : Tally × List Tally) : Block 2 k → Block 2 k :=
  underPrefix (chunkFactor k) (crossResidueMask (r := q.1.length) (posGuard k) (packedRead q.2))

/-- The charged operation has exactly the serialized instruction's bit action,
including every native remainder position. -/
theorem packedPass_bits {k : ℕ} (q : Tally × List Tally) (h : WellFormed k (guardWidth k) (packed q))
    (y : Block 2 k) : prefixBit (packedPass q y) = passAction (guardWidth k) (prefixBit y) (packed q) := by
  have hr : q.1.length < guardWidth k := h.1
  obtain ⟨⟨a,b⟩,rfl⟩ := (prefixView (chunkFactor k)).cast.surjective y
  rw [passAction_packedRead]
  funext ix
  obtain ⟨u,rfl⟩ := (threeChunksWithTail k).symm.surjective ix
  cases u with
  | inr j => simp only [packedPass,underPrefix_pair,gathered,Equiv.apply_symm_apply,tailPrefixBit]
  | inl cj =>
    obtain ⟨c,j⟩ := cj
    simp only [packedPass,underPrefix_pair,gathered,Equiv.apply_symm_apply,bulkPrefixBit,
      crossResidueMask_read (posGuard _) hr]
    have ch (c : Fin 3) : chunkWord (prefixBit ((prefixView (chunkFactor k)).cast (a,b))) c =
        fun j => crossBits b (c.rev,j) := funext (bulkPrefixBit k a b c)
    simp only [ch]
    fin_cases c <;> simp [Fin.rev]

/-- The packed payload is obtained by projecting off its two sum-constructor tags. -/
theorem packedPayload_has {X : Type} {R : Regime X} {q : X → Tally × List Tally}
    (h : R.Has (fun x => packed (q x))) : R.Has q := by
  have tagged : R.Has (fun x => (true,false,q x)) := h
  exact tagged.ez (Easy.snd.compose Easy.snd)

/-- Uniform physical command for the packed opcode. The input regime supplies
only the native width and the actual opcode. -/
theorem packedPassStage {X : Type} {R : Regime X} {l : X → ℕ} (k : X → ℕ)
    (q : X → Tally × List Tally) (hk : Realizes R k) (opcode : R.Has fun x => packed (q x))
    (valid : ∀ x, WellFormed (k x) (guardWidth (k x)) (packed (q x)))
    (ρ : ℝ) (hρ : 1/2 < ρ) {U : X → Type} (u : (x : X) → Series (U x))
    (z : ∀ x, (u x).count ≤ l x) (f : (x : X) → Block 2 (k x) → U x → Bead) :
    let flat x := line 2 (k x)
    Breeze (Spindle.modes k (τ := ρ)) R (fun x => (flat x).count) l
      (together R.header (cloth flat u f)) (cloth flat u (fun x y => f x (packedPass (q x) y))) := by
  have payload := packedPayload_has opcode
  have n := third_realizes hk
  have hn := (n.plus n).plus n
  have g := guardWidth_realizes hk
  have r : Realizes R (fun x => (q x).1.length) := by
    have hd := payload.ez Easy.fst
    change R.Has (fun x => tally (q x).1.length)
    simpa only [recover_tally] using hd
  have ht : R.Has (fun x => List.ofFn (fun j : Fin (k x/3) =>
      tally (((packedRead (q x).2 j).map Fin.val).getD (k x/3)))) := by
    simpa only [packedRead_table (valid _)] using (payload.ez Easy.snd)
  apply binaryPrefixPass (fun x => k x%3) (fun x => crossWidth (k x/3)) k
    (fun x => chunkFactor (k x)) (thirdRemainder_realizes hk) hn u z
    (fun x => crossResidueMask (r := (q x).1.length) (posGuard (k x)) (packedRead (q x).2)) _ f
  intro fs
  let Y := (x : X) × Block 2 (k x%3)
  let atX : Y → X := Sigma.fst
  let N := fun y : Y => k (atX y)/3
  let G := fun y : Y => guardWidth (k (atX y))
  let residue := fun y : Y => (q (atX y)).1.length
  have nonneg : 0 ≤ ρ := by linarith
  apply crossResidueStage_atRate (R := R.pull atX) N G residue
    (fun y => packedRead (q (atX y)).2) (fun y => posGuard _) (Task.BT.map n atX)
    (Task.BT.map g atX) (Task.BT.map r atX) (Task.BT.map ht atX) _ ρ
    (nearRoot_rectInterchange hρ _ _) (fun y => u y.1) (fun y => z y.1) nonneg
    (fun y => Spindle.modes k (τ := ρ) y.1) (fun y => Spindle.belly _ nonneg y.1) _ fs
  · intro y
    exact crossSparse (posGuard _) y.property (Nat.div_le_self ..) le_rfl
  · intro y
    have hf := crossFit (posGuard _) y.property
    have h₁ : crossExtent (N y) (G y) (residue y) ≤ k y.val.1 := by
      have := Nat.div_le_self (k y.val.1) 3
      change residue y + crossExtent (N y) (G y) (residue y) ≤ k y.val.1/3 at hf
      omega
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right h₁ 1) nonneg

end
end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
