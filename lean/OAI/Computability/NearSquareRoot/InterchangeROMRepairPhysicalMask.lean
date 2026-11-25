import OAI.Computability.NearSquareRoot.InterchangeSpectralMask
import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksShape
import OAI.Computability.NearSquareRoot.InterchangeROMTableMask
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # A single comparison scanner for all active request shapes and radices

The primitive consumes the unary radix and the ordinary field request header. It
builds four unary rulers and expands the ordered comparison at every native
record. Its P192 program and register cutoff do not depend on the geometry.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Mask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeSpace NearSquareRoot.Space
  NearSquareRoot.InterchangeROMLeafMasksShape

abbrev mark (v : Ordering) := InterchangeROMTable.comparisonMark (InterchangeROMTable.comparisonCode v)

noncomputable def output {b : ℕ} (x : Request b) :=
  stripe x.rows fun z => mark (InterchangeSpectralStep.direction (number z.2.1) (number z.2.2.2.1))

open private counts from OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksShape

private theorem rulerScan {I : Type} (b : I → ℕ) (x : (i : I) → Request (b i))
    (hb : ∀ i, 2 ≤ b i)
    (valid : ∀ i, solid (x i).before ∧ solid (x i).between ∧ solid (x i).after_) :
    BoundedTask (fun i => (x i).rows.count) (fun i => (x i).rows.count)
      (fun i => send (rulers (x i))) (fun i => output (x i)) := by
  let p i := layout (x i).before
  let h i := line (b i) (x i).width
  let g i := layout (x i).between
  let z i := layout (x i).after_
  let N i := (x i).rows.count
  let w (i : I) : ℝ := N i
  have nCount i : N i = (p i).count * ((h i).count * ((g i).count * ((h i).count * (z i).count))) := by
    change (((p i).cart ((h i).cart ((g i).cart ((h i).cart (z i)))))).count = _
    simp only [Series.count_cart]
  have pp i : 0 < (p i).count := by simpa only [p,Dims.space] using wide _ (valid i).1
  have hp i : 0 < (h i).count := by
    dsimp only [h]; rw [lineSize]; exact Nat.pow_pos (by have := hb i; omega)
  have gp i : 0 < (g i).count := by simpa only [g,Dims.space] using wide _ (valid i).2.1
  have zp i : 0 < (z i).count := by simpa only [z,Dims.space] using wide _ (valid i).2.2
  have one i : 1 ≤ w i := by
    dsimp only [w]; rw [nCount]; exact_mod_cast Nat.mul_pos (pp i) (Nat.mul_pos (hp i) (Nat.mul_pos (gp i) (Nat.mul_pos (hp i) (zp i))))
  have fit i := counts (p i).count (h i).count (g i).count (z i).count (pp i) (hp i) (gp i) (zp i)
  have sizeBound : Volume w (fun i => send (rulers (x i))) := by
    refine ⟨20,fun i => ?_⟩
    change (size (rulers (x i)) : ℝ) ≤ (20:ℕ) * (N i : ℝ)
    have e := fit i
    have e' := nCount i
    have positive := (Nat.mul_pos (pp i) (Nat.mul_pos (hp i) (Nat.mul_pos (gp i) (Nat.mul_pos (hp i) (zp i)))))
    have num : size (rulers (x i)) ≤ 20 * N i := by
      change size (tally (p i).count,tally (h i).count,tally (g i).count,tally (z i).count,
        tally ((g i).count*((h i).count*(z i).count))) ≤ 20*N i
      simp only [size_prod,size_tally,tally_length]
      omega
    exact_mod_cast num
  let read := fun (f : (Tally × Tally × Tally × Tally × Tally) → Tally) (run : Easy f) =>
    Carries.func one sizeBound f run
  have pR := read Prod.fst (by fun_prop)
  have hR := read (fun a => a.2.1) (by fun_prop)
  have gR := read (fun a => a.2.2.1) (by fun_prop)
  have zR := read (fun a => a.2.2.2.1) (by fun_prop)
  have reduced (i : I) : (((h i).count * ((h i).count * (z i).count) : ℕ) : ℝ) ≤ w i := by
    dsimp only [w]
    rw [nCount]
    exact_mod_cast (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (gp i))).trans
      (Nat.le_mul_of_pos_left _ (pp i))
  have nested := SpectralHeaders.nestedMasks h z hp zp (mark .gt) (mark .eq) (mark .lt)
    reduced hR zR
  have hc (i : I) (a y : Block (b i) (x i).width) :
      SpectralRuns.mask (h i) ((h i).index a) (mark .gt) (mark .eq) (mark .lt) y =
        mark (InterchangeSpectralStep.direction (number a) (number y)) := by
    let : NeZero (b i) := ⟨by have := hb i; omega⟩
    rw [← SpectralMask.rankTag_number]
    unfold SpectralRuns.mask SpectralMask.rankTag
    dsimp only [h]
    split_ifs <;> rfl
  simp_rw [hc] at nested
  let tail (i : I) := (h i).cart (z i)
  let f (i : I) (a : Block (b i) (x i).width) (c : Block (b i) (x i).width × Pin (x i).after_) :=
    mark (InterchangeSpectralStep.direction (number a) (number c.1))
  have sizeMark (o : Ordering) : (mark o).count ≤ 3 := by cases o <;> decide
  have ex := SpectralTile.tile p h g tail f pp hp gp (fun i => by
      simp only [tail,Series.count_cart]; exact Nat.mul_pos (hp i) (zp i))
    3 (fun i a c => sizeMark _) (fun i => by simp only [tail,Series.count_cart,w,nCount]; rfl)
    pR hR gR nested
  apply (carries_bounded ex).conform (fun i => Nat.ceil_natCast _) (fun i => Nat.ceil_natCast _) (fun i => rfl)
  intro i
  rfl

abbrev Shape := { s : Sigma Request // 2 ≤ s.1 ∧ solid s.2.before ∧ solid s.2.between ∧ solid s.2.after_ }

/-- The physical code is chosen once from a domain containing all legal
descriptor and radix values; the width and the tapes are runtime inputs. -/
theorem universal :
    BoundedTask (fun s : Shape => cost s.val.2) (fun s : Shape => cost s.val.2)
      (fun s => .fork (send (tally s.val.1)) s.val.2.header) (fun s => output s.val.2) := by
  let b (s : Shape) := s.val.1
  let x (s : Shape) := s.val.2
  have p := prepare_solid b x (fun s => s.property.1) (fun s => s.property.2)
  have q := rulerScan b x (fun s => s.property.1) (fun s => s.property.2)
  have large (s : Shape) : (x s).rows.count ≤ cost (x s) := Nat.le_add_right _ _
  apply (p.compose q).bound 2 1
  · intro s
    change cost (x s) + (x s).rows.count + 1 ≤ 2 * (cost (x s) + 1)
    have := large s
    simp only [two_mul]
    omega
  · intro s
    rw [max_eq_left (large s), one_mul]

noncomputable def scanner : Cmd := universal.forget.choose

theorem scanner_fits : ∃ K, ∀ {b : ℕ} (x : Request b) (_ : 2 ≤ b) (_ : solid x.before)
    (_ : solid x.between) (_ : solid x.after_) (env : Env) (r : Deck),
    Fits env scanner (pile 0 (.fork (send (tally b)) x.header) r) (pile 0 (output x) r)
      (K * (cost x + 1)) := by
  obtain ⟨K,hK⟩ := universal.forget.choose_spec
  refine ⟨K, fun {b} x hb hp hg hs env r => ?_⟩
  let s : Shape := ⟨⟨b,x⟩,hb,hp,hg,hs⟩
  exact hK s env r

end InterchangeROMRepair.Physical.Mask

end NearSquareRoot
end Computability
end OAI
