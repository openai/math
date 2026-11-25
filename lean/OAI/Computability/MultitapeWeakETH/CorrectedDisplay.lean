import OAI.Computability.MultitapeWeakETH.FoldedDisplay

/-! # Corrected singleton slices display the shifted payload at both endpoints -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open VPVNP VPVNP.WireTensor
open scoped Classical
noncomputable section

variable {n b N L : ℕ} [NeZero N] (G : Network n b) {K : Type} [Field K]

def errorMasks (b : ℕ) (z : Fin 4 → Word n) (target : Fin 4 → Fin (2^n))
    (r : Fin 4) (j : Block n b) : Word b :=
  Difference.maskFor (Difference.message b j.val (List.ofFn (z r)).reverse)
    (Difference.message b j.val (BurstRAM.wordBits (target r)))

def difference (target : Fin 4 → Fin (2^n)) (lane : Bool) :=
  target (column lane false) - target (column lane true)

def carryAfter (target : Fin 4 → Fin (2^n)) (j : Block n b) (lane : Bool) :=
  Difference.borrow (BurstRAM.wordBits (target (column lane false))) (BurstRAM.wordBits (target (column lane true)))
    ((j.val+1)*b)

def diffBlock (target : Fin 4 → Fin (2^n)) (j : Block n b) (lane : Bool) :=
  Difference.message b j.val (BurstRAM.wordBits (difference target lane))

theorem corrected_step (z : Fin 4 → Word n) (target : Fin 4 → Fin (2^n)) (j : Block n b) :
    pairedStep j (fun i => errorMasks b z target i j)
      (fun i => Difference.message b j.val (List.ofFn (z i)).reverse)
      (if j.val=0 then fun _ => false else carryAfter target ((finRotate _).symm j)) =
      (diffBlock target j,carryAfter target j) := by
  have carry (lane : Bool) :
      (if j.val=0 then (fun _ : Bool => false) else carryAfter target ((finRotate _).symm j)) lane =
        Difference.borrow (BurstRAM.wordBits (target (column lane false)))
          (BurstRAM.wordBits (target (column lane true))) (j.val*b) := by
    by_cases zero : j.val = 0
    · simp [zero,Difference.borrow,TapeWord.scan]
    · let _ : NeZero (n ⌈/⌉ b) := ⟨by have := j.isLt; omega⟩
      have prev := coe_finRotate_symm_of_ne_zero (i:=j) (fun eq => zero (congrArg Fin.val eq))
      simp only [zero,ite_false,carryAfter,prev,show j.val-1+1=j.val by omega]
  have run (lane : Bool) := Difference.process_residues b j.val (target (column lane false))
    (target (column lane true)) (Difference.message b j.val (List.ofFn (z (column lane false))).reverse)
      (Difference.message b j.val (List.ofFn (z (column lane true))).reverse)
  apply Prod.ext
  · funext lane
    simp only [pairedStep,carry,errorMasks,diffBlock,difference]
    exact congrArg Prod.fst (run lane)
  · funext lane
    simp only [pairedStep,carry,errorMasks,carryAfter]
    exact congrArg Prod.snd (run lane)

def position (s : ℕ) (fits : s+L ≤ n) (j : Fin L) : Fin n := ⟨s+j.val,by have := j.isLt; omega⟩

/-- A shift uses its own four columns, masks and bit intervals on the common
supply. The local matrices depend only on the tables, positions and site pin,
so the same matrices serve every good row in the fixed four-column slice. -/
theorem corrected_display (hb : 0 < b) (s u : ℕ) (fits : s+u+L ≤ n)
    (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (x : Word n) (z : Fin 4 → Word n) (scalar : Fin 4 → K)
    (returns : ∀ i w, G.contract (tables i) x w = if w = z i then scalar i else 0)
    (target : Fin 4 → Fin (2^n)) (w : Fin (2^L))
    (first : (difference target false).val / 2^s % 2^L = w.val)
    (second : (difference target true).val / 2^(s+u) % 2^L = w.val) :
    let l := position s (show s+L ≤ n by omega)
    let r := position (s+u) fits
    applyLocal (fun v => maps G hb l r tables v (pinFor G x (errorMasks b z target) v))
        (typedSupply G K (N:=N)).coeff =
      fun ext => if ext = edgeAssignment (destination G hb ∘ l) (destination G hb ∘ r)
        (fun j : Fin L => w.val.testBit j.val) then ∏ i, scalar i else 0 := by
  intro l r
  apply display G hb l r tables x _ z scalar returns (carryAfter target) (diffBlock target)
    (corrected_step z target)
  · intro j
    exact (Difference.message_bit hb (difference target false) (l j).val (l j).isLt).trans
      (Difference.payload_bit _ _ first j)
  · intro j
    exact (Difference.message_bit hb (difference target true) (r j).val (r j).isLt).trans
      (Difference.payload_bit _ _ second j)

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
