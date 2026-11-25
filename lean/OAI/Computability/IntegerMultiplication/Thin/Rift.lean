import OAI.Computability.IntegerMultiplication.Thin.Mirror

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Code Strip Dims Adic Packed Earth Loom Iter
noncomputable section
variable {I : Type} {r:Regime I}
private theorem aug {c L:I→ℕ} (s : r.Has (tally ∘ c))
    (h : r.Has (tally ∘ L)) :
    r.Has fun i=> tally (c i+L i) := by
  simpa only [Function.comp_def,Dims.mergeTally] using (s.pair h).ez Easy.append
variable (c L d b w : I→ℕ) (v : ℕ)
abbrev Mn (i:I) := tn (c i) (L i) (d i) (b i)
variable (s : r.Has (tally ∘ c)) (h : r.Has (tally ∘ L))
    (g : r.Has (tally ∘ d)) (u : r.Has (tally ∘ b))
include s h g u
theorem rift (x : (i:I)→Land (c i) (L i) (d i) (b i)→Tree)
    (a : ∀ i z,(x i z).count ≤ v*(w i+1)) :
    let P i := lands (c i) (L i) (d i) (b i)
    Breeze (fun i=> (L i:ℝ)+1) r single (rolls (Mn c L d b) w)
      (together r.header (stackRun P x))
      (stackRun P fun i=> x i ∘ switch_) := by
  let N := Mn c L d b
  let A (i:I) := bolt_ (c i) (L i) (d i) (b i)
  let x0 (i:I) := x i ∘ (A i).cast.symm
  let q i := tour (c i) (L i) (d i) (b i)
  have Hw := aug (aug (aug (aug s h) g) h) u
  have Hs : r.Has fun i=> screen (q i) := by
    let f : (Tally×Tally)×Tally→Tally×Tally := fun j=> (j.1.1 ++ j.2,j.1.2 ++ j.2)
    have c := Poly.push ([],([]:Tally)) ([]:Tally) (show Poly f from (Easy.poly (by unfold f; fun_prop)))
    have d := h.thenDo poly_line
    have v := ((s.pair (aug (aug s h) g)).pair d).thenDo c
    simpa only [Function.comp_def,screen,q,tour,twin,nearby,afar,polyPush,lined,f,
      List.map_ofFn, Dims.mergeTally] using v
  have T := glide N w L q Hs Hw h (fun i j=> sep ..) v x0 (fun i z=> a i _)
  have Y (i:I) (f : Byte (N i)→Tree) := (A i).packet f
  change Breeze _ _ _ _ (together r.header (fun i=> stripe (line 2 _) (x0 i)))
    (fun i=> stripe (line 2 _) (x0 i ∘ lever (voyage N L q i))) at T
  simp_rw [Y] at T
  unfold x0 voyage N q A at T
  simp only [Function.comp_def,Equiv.symm_apply_apply,IntegerMultiplication.Thin.sight,Equiv.symm_apply_apply] at T
  exact T
end
end Thin

end IntegerMultiplication
end Computability
end OAI
