import OAI.Computability.IntegerMultiplication.Bureau.Valor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Param Scale Halo Strip Dims Adic Phase Hook Code Brief Staff Net Loom Cone Grid
variable {I:Type} (n:I→ℕ)(h:∀i,Season (n i))
noncomputable section
variable {J A X : Type} [Fintype J] [DecidableEq J] [Fintype A] (d:Phase.Guild J A X Motif.sigma)
variable (v:Series A)
include d v
variable (b:(i:I)→ℕ→G (n i)) (x:(i:I)→Farm (n i))
abbrev freq (i:I):=send (Grid.telex (Scale.F (n i)) (ell (n i)) (b i))
abbrev possession (i:I):=singlet (h i) (x i)
abbrev tide := fun (i:I)=> Ho (h i) (b i) (x i)

include h
set_option maxHeartbeats 2200000 in
/-- transfer theorem.  Starts with telex (to be generated globally) -/
theorem prices :
    Spun n (hue n) (together (freq n b) (possession n h x)) (possession n h (tide n h b x)) := by
  let c:= guide_journals n
  have O : (journals n).Has (fun i=>List.ofFn (boat n i)):= Brief.camera n c
  have R (i:I): ((Peace (n i)).count+1)*(hw n i+1) ≤ fU n i := by rw [tallZ]; rfl
  have S i : Phase.safe (Hf n i) (Hj n i):=(h i).safe.1
  have Q i : Phase.safe (Hf n i) (Hy n i):=(h i).safe.2.1
  have T i : (Hf n i)≤hw n i+1 := (Nat.sub_le ..).trans ((Nat.le_self_pow (by decide) (_:ℕ):lanes (n i)≤P (n i)).trans
    ((digitRoom ..).trans (Nat.le_succ _)))
  have D i : 1≤ Hf n i := by change 1≤lanes (n i)-2; have v:=(h i).dim; omega
  have L i : altitude (Hg n) (Hj n) (Hy n) i≤ hw n i+1 := by
    rw [show altitude _ _ _ i=ell (n i) from breadth (h i)]
    have g:= wall_small (n i)
    exact (le_trans (Nat.le_mul_of_pos_left _ (lanes_pos (n i))) g).trans ((digitRoom ..).trans (Nat.le_succ _))
  have U i : (2^altitude (Hg n) (Hj n) (Hy n) i)*(hw n i+1) ≤ fU n i := by
    rw [show altitude _ _ _ i=ell (n i) from breadth (h i)]
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have W i : hv n i ≤ hw n i+1 := by unfold hv hw Scale.F Scale.W Function.comp; change 4096*P (n i)≤8192*P (n i)+1; omega
  let p i:= harness (h i) (x i)
  have u:=Grid.sheer d v Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) (fU n) (hv n) (T:=hab n)
    (fun i=> Peace (n i)) (paper n c) (c.positions n) (c.jumps n)
    (c.generator n) (c.excess n) R S Q T D (boat n) O (Hj n)
    (faces ∘ n) (trace_ ∘ n) (card_ n h c) b W L U p
  let C:=Hook.crate Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) (T:=hab n) (fun i=>Peace (n i))
  let w (i:I):=essay n b i (p i)
  let r i:=send (Grid.call (Hg n) (Hj n) (Hy n) (hw n) (hv n) b i)
  have eqn : r=freq n b:=funext (fun i=> by
    change send (telex (hv n i) (altitude (Hg n) (Hj n) (Hy n) i) _)=_
    rw [show altitude _ _ _ i=ell (n i) from breadth (h i)]
    rfl)
  change Breeze (stageL n) (logs n) (dim n) (fU n)
    (together (cell n) (together r (C p))) (C w) at u
  have prodn (x:(i:I)→Farm (n i)):
      C (fun i=>harness (h i) (x i)) = possession n h x :=
    funext fun i=> plate (h i) (x i)
  have E:w=(fun i=>harness (h i) (tide n h b x i)) :=
    funext fun i=> lyric n h b i (x i)
  unfold p at u
  rw [eqn,prodn,E,prodn] at u
  exact allow_B n h u

-- generate table
variable (p:(Brief.city n).Has (fun i=>Grid.telex (Scale.F (n i)) (ell (n i)) (b i)))
include p
theorem aims :
    Spun n (hue n) (possession n h x) (possession n h (tide n h b x)) :=
  transport (inherit (((rescue (ocean n h x) p):Wood n (possession n h x) (freq n b)).twice (me (ocean n h x))) (color_p n)) (prices n h d v b x)
end
end Bureau

end IntegerMultiplication
end Computability
end OAI
