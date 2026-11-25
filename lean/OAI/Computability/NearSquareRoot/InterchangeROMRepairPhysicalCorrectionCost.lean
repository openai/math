import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionLeaf

/-! # Linear local volume and clocks for the packed correction leaf -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters GeneratorSyntax InterchangeROMTable InterchangeROM

private theorem forest_upper {A : Type} (v : A → Tree) (l : List A) (B : ℕ)
    (h : ∀ a ∈ l, (v a).count ≤ B) : (Task.forest v l).count ≤ (B+1)*l.length + 1 := by
  induction l with
  | nil => simp [Tree.count]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hh := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [Task.forest_cons,Tree.count,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private theorem stripe_upper {A : Type} (v : A → Tree) (rows : Series A) (B : ℕ)
    (h : ∀ a, (v a).count ≤ B) : (stripe rows v).count ≤ (B+1)*rows.count+1 := by
  rw [stripe_simple]
  exact forest_upper _ _ B (fun a _ => h a)

private theorem nested_upper {A : Type} {P : A → Type} (rows : Series A) (payload : (a : A) → Series (P a))
    (width B : ℕ) (hw : ∀ a, (payload a).count ≤ width) (v : (a : A) → P a → Tree)
    (hv : ∀ a j, (v a j).count ≤ B) :
    (stripe rows fun a => stripe (payload a) (v a)).count ≤ (B+3)*(rows.count*(width+1)+1) := by
  have hi (a : A) : (stripe (payload a) (v a)).count ≤ (B+1)*width+1 :=
    (stripe_upper _ _ _ (hv a)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (hw a)) _)
  refine (stripe_upper _ _ _ hi).trans ?_
  nlinarith

private theorem numeral_count (k : ℕ) : (numeral k).count = 2*k+1 := by
  change size (tally k) = _
  rw [size_tally,tally_length]

/-- Coefficient of the local record volume, excluding the separately compiled
one-shot compact header reader. -/
def linearFactor (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :=
  kernelFactor p s m t oi ii + 1200*((ii.length+1)*(2*p+8) + 4*(2^m)+9)

theorem clock_le {A D : Type} {P : A → Type} {p s m : ℕ}
    (header : Tree) (maskTime : ℕ) (t : Raw.Tape) (η : A → Fin m → Bool)
    (src dst : Series (D × Fin s)) (lane : D → ℕ)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ) (hw : ∀ a, (payload a).count ≤ width)
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1)) :
    let ii := (twoBlocks src).tab (checkIndex lane)
    let oi := (twoBlocks dst).tab (checkIndex lane)
    let tag a := numeral (Raw.mask (η a)).val
    let xs := encodedBank src rows payload (v false) ++ encodedBank src rows payload (v true)
    localClock header (Task.forest id xs) (stripe rows tag) (broadcast rows payload tag)
      maskTime (kernelFactor p s m t oi ii * (rows.count*(width+1)+1)) ≤
      maskTime + 1200*header.count + linearFactor p s m t oi ii * (rows.count*(width+1)+1) := by
  intro ii oi tag xs
  let M := rows.count*(width+1)+1
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have hr : rows.count ≤ M := by dsimp only [M]; nlinarith
  have len : xs.length = ii.length := by simp [xs,ii,twoBlocks,encodedBank,Series.tab]
  have hd (b : Bool) (u : D × Fin s) :
      (encodedRow rows payload fun a j => v b u.1 a j u.2).count ≤ (2*p+6)*M := by
    apply (nested_upper rows payload width (2*p+3) hw _ ?_).trans (by simp [M])
    intro a j
    rw [numeral_count]
    dsimp only
    have hp := ZMod.val_lt (v b u.1 a j u.2)
    omega
  have hx : (Task.forest id xs).count ≤ ((ii.length+1)*(2*p+8))*M := by
    have := forest_upper id xs ((2*p+6)*M) (by
      intro row hrow
      rcases List.mem_append.mp hrow with h|h
      all_goals
        obtain ⟨u,rfl⟩ := Series.elements _ _ _ |>.mp h
        apply hd)
    rw [len] at this
    apply this.trans
    nlinarith
  have htag (a : A) : (tag a).count ≤ 2*(2^m)+1 := by
    dsimp only [tag]; rw [numeral_count]
    have := (Raw.mask (η a)).isLt
    omega
  have hn := (stripe_upper tag rows _ htag).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hr) _)
  have hw' := nested_upper rows payload width _ hw (fun a _ => tag a) (fun a _ => htag a)
  change (broadcast rows payload tag).count ≤ _ * M at hw'
  change _ ≤ (2*2^m+1+1)*M+1 at hn
  dsimp only [localClock,linearFactor]
  change _ ≤ maskTime+1200*header.count+(_+1200*(_+4*2^m+9))*M
  change maskTime + _*M + 1200*(header.count + _ + _ + _ + 1) ≤ _
  nlinarith

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
