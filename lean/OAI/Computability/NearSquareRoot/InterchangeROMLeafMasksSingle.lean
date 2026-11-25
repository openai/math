import OAI.Computability.NearSquareRoot.InterchangeSpectralTile
import OAI.Computability.NearSquareRoot.InterchangeSpectralRuns
import OAI.Computability.IntegerMultiplication.Carry.Small

/-! # One variable leaf class in native rectangular row order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeafMasks

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Bits IntegerMultiplication.Carry

abbrev Head := Tally × Tally × Tally × Tally × Tally
abbrev Query := Head × Tally × Tally

def head (p d g s : ℕ) : Head :=
  (tally p,tally d,tally g,tally s,tally (g*(d*s)))

def query (p d g s u v : ℕ) : Query := (head p d g s, tally u, tally v)

private def early (q : Query) := (born q.2.1.length,born q.1.2.1.length,born q.1.2.2.2.2.length)
private def late (q : Query) := (born q.2.2.length,born q.1.2.1.length,born q.1.2.2.2.1.length)

private theorem joint_mask {A : Type} (h : Series A) (u : Fin h.count) (x : A) :
    SpectralRuns.mask h u false true false x = decide (h.index x = u) := by
  by_cases t : h.index x < u
  · simp [SpectralRuns.mask,t,t.ne]
  · by_cases e : h.index x = u <;> simp [SpectralRuns.mask,t,e]

variable {I : Type} {P H G B : I → Type} (p : (i : I) → Series (P i))
    (h : (i : I) → Series (H i)) (g : (i : I) → Series (G i)) (b : (i : I) → Series (B i))
    (pp : ∀ i, 0 < (p i).count) (ph : ∀ i, 0 < (h i).count)
    (pg : ∀ i, 0 < (g i).count) (pb : ∀ i, 0 < (b i).count)
    (u v : (i : I) → Fin (h i).count)

abbrev rows (i : I) := (p i).cart ((h i).cart ((g i).cart ((h i).cart (b i))))

include pp ph pg pb in
/-- The ranks and all five counts are read from the input. One P192 command
forms the early and late comparison runs, duplicates whole runs over the
spectators, and takes their pointwise conjunction. -/
theorem single : Task (fun i => (rows p h g b i).count) (fun i => send
    (query (p i).count (h i).count (g i).count (b i).count (u i).val (v i).val))
    (fun i => send ((rows p h g b i).tab fun x =>
      decide ((h i).index x.2.1 = u i ∧ (h i).index x.2.2.2.1 = v i))) := by
  let N i := (p i).count * ((h i).count * ((g i).count * ((h i).count * (b i).count)))
  let sh i := query (p i).count (h i).count (g i).count (b i).count (u i).val (v i).val
  let w i := (N i:ℝ)
  let tail i := (g i).cart ((h i).cart (b i))
  have ds (i : I) : 0 < (h i).count * (b i).count := Nat.mul_pos (ph i) (pb i)
  have gs (i : I) : 0 < (tail i).count := by simpa only [tail,Series.count_cart] using Nat.mul_pos (pg i) (ds i)
  have a (i : I) : 0 < (h i).count * (tail i).count := Nat.mul_pos (ph i) (gs i)
  have aa (i : I) : (h i).count * (tail i).count ≤ N i := by
    simpa only [tail,Series.count_cart] using Nat.le_mul_of_pos_left ((h i).count * ((g i).count*((h i).count*(b i).count))) (pp i)
  have gg (i : I) : (tail i).count ≤ N i :=
    (Nat.le_mul_of_pos_left _ (ph i)).trans (aa i)
  have bb (i : I) : (h i).count * (b i).count ≤ N i := (Nat.le_mul_of_pos_left _ (pg i)).trans (by simpa only [tail,Series.count_cart] using gg i)
  have positive (i : I) : 1 ≤ w i := by
    dsimp only [w]
    exact_mod_cast (show 1 ≤ N i from Nat.mul_pos (pp i) (Nat.mul_pos (ph i) (Nat.mul_pos (pg i) (ds i))))
  have vol : Volume w (send ∘ sh) := by
    refine ⟨28, fun i => ?_⟩
    have c₁ : (p i).count ≤ N i := Nat.le_mul_of_pos_right _ (Nat.mul_pos (ph i) (Nat.mul_pos (pg i) (ds i)))
    have c₂ : (h i).count ≤ N i := (Nat.le_mul_of_pos_right _ (pb i)).trans (bb i)
    have c₃ : (g i).count ≤ N i := (Nat.le_mul_of_pos_right _ (ds i)).trans (by simpa only [tail,Series.count_cart] using gg i)
    have c₄ : (b i).count ≤ N i := (Nat.le_mul_of_pos_left _ (ph i)).trans (bb i)
    have c₅ := gg i
    simp only [tail,Series.count_cart] at c₅
    have Npos := c₁.trans' (pp i)
    have ru := (u i).isLt
    have rv := (v i).isLt
    have vv : size (sh i) ≤ 28*N i := by
      simp only [sh,query,head,size_prod,size_tally,tally_length]
      omega
    change ((size (sh i)):ℝ) ≤ 28*w i
    dsimp only [w]
    exact_mod_cast vv
  have pick {X : Type} [Codec X] (f : Query → X) (easy : Easy f) :=
    Carries.func (y:=sh) positive vol f easy
  have chart (f : Query → Tally) (hf : Easy f) : Easy (fun z => born (f z).length) := hf.compose easy_chart
  have rank₁ := pick early ((chart (fun q => q.2.1) (by fun_prop)).pair
    ((chart (fun q => q.1.2.1) (by fun_prop)).pair (chart (fun q => q.1.2.2.2.2) (by fun_prop))))
  have rank₂ := pick late ((chart (fun q => q.2.2) (by fun_prop)).pair
    ((chart (fun q => q.1.2.1) (by fun_prop)).pair (chart (fun q => q.1.2.2.2.1) (by fun_prop))))
  have ea : Carries w (send ∘ sh)
      (fun i => stripe ((h i).cart (tail i)) fun x => send (decide ((h i).index x.1 = u i))) := by
    apply rank₁.chain
    simpa only [early,sh,query,head,tally_length,Function.comp_def,tail,Series.count_cart,joint_mask] using
      (SpectralRuns.fibre_stripe h tail gs u false true false).larger
        (show ∀ i, (((h i).count * (tail i).count : ℕ):ℝ) ≤ w i from fun i => by dsimp only [w]; exact_mod_cast aa i)
  have la : Carries w (send ∘ sh)
      (fun i => stripe ((h i).cart (b i)) fun x => send (decide ((h i).index x.1 = v i))) := by
    apply rank₂.chain
    simpa only [late,sh,query,head,tally_length,Function.comp_def,joint_mask] using
      (SpectralRuns.fibre_stripe h b pb v false true false).larger
        (show ∀ i, (((h i).count * (b i).count : ℕ):ℝ) ≤ w i from fun i => by dsimp only [w]; exact_mod_cast bb i)
  have hp := pick (fun q => q.1.1) (by fun_prop)
  have hh := pick (fun q => q.1.2.1) (by fun_prop)
  have hg := pick (fun q => q.1.2.2.1) (by fun_prop)
  let emit {A C : I → Type} (s : (i:I) → Series (A i)) (t : (i:I) → Series (C i))
      (f : (i:I) → C i → Bool) (ps : ∀ i, 0 < (s i).count) (pt : ∀ i, 0 < (t i).count)
      (count : Carries w (send ∘ sh) (fun i => send (tally (s i).count)))
      (body : Carries w (send ∘ sh) (fun i => stripe (t i) fun x => send (f i x)))
      (fits : ∀ i, (s i).count * (t i).count ≤ N i) :=
    SpectralTile.repeatFlat s t (fun i x => send (f i x)) ps pt 1 (fun _ _ => le_rfl) (count.twice body)
      (fun i => by dsimp only [w]; exact_mod_cast fits i)
  have left := emit p (fun i => (h i).cart (tail i)) (fun i x => decide ((h i).index x.1 = u i))
    pp (fun i => by simpa only [Series.count_cart] using a i) hp ea (fun i => by simp only [Series.count_cart,tail,N]; rfl)
  let lateEq i (a : G i × H i × B i) := decide ((h i).index a.2.1 = v i)
  have inner := emit g (fun i => (h i).cart (b i)) (fun i x => decide ((h i).index x.1 = v i))
    pg (fun i => by simpa only [Series.count_cart] using ds i) hg la (fun i => by simpa only [tail,Series.count_cart] using gg i)
  have mid := emit h tail lateEq ph gs hh inner aa
  have right := emit p (fun i => (h i).cart (tail i)) (fun i x => lateEq i x.2) pp (fun i => by simpa only [Series.count_cart] using a i) hp mid (fun i => by simp only [Series.count_cart,tail,N]; rfl)
  let rs := rows p h g b
  let lhs (i : I) (x : P i × H i × G i × H i × B i) := decide ((h i).index x.2.1 = u i)
  let rhs (i : I) (x : P i × H i × G i × H i × B i) := decide ((h i).index x.2.2.2.1 = v i)
  have pair := coalesce rs (fun i x => send (lhs i x)) (fun i x => send (rhs i x)) left right
  let digits i := (rs i).tab (fun x => (lhs i x,rhs i x))
  change Carries w (send ∘ sh) (fun i => stripe (rs i) fun x => send (lhs i x,rhs i x)) at pair
  simp_rw [stripe_eq'] at pair
  have run := pair.chain (Carries.func (y:=digits) positive pair.out
    (List.map (fun z : Bool × Bool => z.1 && z.2)) (Easy.finite _).mapping)
  obtain ⟨_,steps,cmd,K,bound⟩ := run.runs
  apply (cmd.bound K (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  · have hb' := bound i
    dsimp only [w] at hb'
    have z : steps i + 1 ≤ K * N i := by exact_mod_cast hb'
    simpa only [rows,Series.count_cart,N] using z.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · simp only [digits,Function.comp_def,Series.map_tab,rs,lhs,rhs]
    apply congrArg send
    apply congrArg ((rows p h g b i).tab)
    funext x
    by_cases x₁ : (h i).index x.2.1 = u i <;> by_cases x₂ : (h i).index x.2.2.2.1 = v i <;> simp [x₁,x₂]

end InterchangeROMLeafMasks

end NearSquareRoot
end Computability
end OAI
