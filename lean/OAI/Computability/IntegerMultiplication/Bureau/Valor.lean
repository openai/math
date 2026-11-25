import OAI.Computability.IntegerMultiplication.Bureau.Radar
import OAI.Computability.IntegerMultiplication.Halo.Lyric

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Param Scale Halo Strip Dims Adic Phase Hook Code Brief Staff Net Loom
variable {I:Type}(n:I→ℕ)(h:∀ i,Season (n i))
abbrev logs := journals n
abbrev sU (n:ℕ):= (Param.wall n+1)*(Scale.W n+1)
abbrev fU := sU ∘ n
abbrev dim := Hook.Globe (fun (_:I)=>[]) (padN ∘ n) (Hf n) (Hg n) (Hj n) (Hy n)
noncomputable section
def hue (i:I):ℝ:= fund (n i)
theorem color_p (i:I):1≤hue n i:=fund1 _

include h
theorem massCap (k:ℕ):
    ∃ D:ℕ,∀ i,mass (logs n) (dim n) (fU n) k i≤ D*token n i := by
  obtain ⟨C,Q⟩ := (Brief.columnRoof n).2 k
  refine ⟨8193*2+C,fun i=>?_⟩
  specialize Q i
  unfold mass token ton
  push_cast
  let y:=n i
  change ((outline y).count:ℝ)* ((sU y : ℝ)+(_)^k) ≤_
  rw [tallH (h i)]
  change (((journals n).scale i+1)^k:ℕ) ≤(C:ℝ)*(Param.room y:ℝ) at Q
  have ew : (1:ℝ)≤ (wall y:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide) : 0<wall y)
  have ep : (1:ℝ)≤ (P y:ℝ) := by exact_mod_cast budget_p y
  have p : (sU y:ℝ) ≤ 2*(wall y:ℝ)*(8193*(P y :ℝ)) := by
    unfold sU; push_cast
    apply mul_le_mul (by linarith) (by exact_mod_cast near_ y) (by positivity) (by positivity)
  push_cast at Q
  have L : (Param.room y : ℝ) ≤ wall y := by exact_mod_cast room_le y
  have u : (sU y:ℝ) +((logs n).scale i+1:ℝ)^k ≤ (wall y:ℝ)* P y*(8193*2+C:ℕ) := by
    push_cast [logs]
    unfold sU at p; push_cast at p
    nlinarith [mul_le_mul_of_nonneg_left L (Nat.cast_nonneg (α:=ℝ) C),
      mul_le_mul_of_nonneg_left ep (show 0≤ (wall y:ℝ)*(C:ℝ) by positivity),
      show (logs n).scale i=(journals n).scale i from rfl] -- invalid Nat equality in nlinarith
  have g : (((Floorplan y).count:ℝ) * wall y)=load y := by
    exact_mod_cast metric (h i)
  calc
    _ ≤ ((Floorplan y).count:ℝ)* ((wall y:ℝ)* P y*(8193*2+C:ℕ)) := by gcongr
    _ = ((8193:ℝ)*2+(C:ℝ))* (load (n i)*(P (n i):ℝ)) := by push_cast; rw [← g]; ring
    _ ≤ _ := by norm_num

abbrev stageL (i:I):ℝ:= Grid.mercy (Hf n) (Hg n) (Hj n) (Hy n)
    (hw n) (Hj n) (faces ∘ n) i
variable {p q:I→Tree}
theorem allow_B (a:Breeze (stageL n) (journals n) (dim n) (fU n) p q):
    Carries (grant n (hue n)) p q := by
  obtain ⟨x,k,t⟩:= a
  obtain ⟨y,M⟩:= massCap n h k
  obtain ⟨c,V⟩:= raise_paid n
  exact Carries.times t (mint_ n (color_p n)) (y*c) (by
    intro i
    apply le_trans (mul_le_mul (M i) (V i) (by linarith [x i]:0≤ stageL n i)
      (by unfold token; positivity))
    unfold grant; push_cast; apply le_of_eq; unfold hue; ring)

-- topology
abbrev edge0 : ∀ k:ℕ,∀ j∈ Adic.field 2 k,j≤Net.Shuttle.base
| 0=> by simp [Adic.field]
| k+1=> by
  intro j h
  rcases List.mem_cons.mp h with h|h
  · subst j; exact Net.Shuttle.base_large.le
  exact edge0 k j h
omit h in
theorem paper {r:Regime I}(g:Guide r n):
    ArrayCards r Hp (Hz n) (hw n) :=
  ⟨Told.nil,Told.carrier (by decide) _ (g.reducedTensor n),
   fun _ a z=> edge0 _ a z,
   (Realizes.fix 8192).times (g.fund n)⟩

abbrev gSlice (r:Regime I):=Hook.Slice r (Hook.norm (Hf n) (Hg n)
  (Hj n) (Hy n)) (chunk ∘ n) (faces ∘ n) (trace_ ∘ n) (hw n)
theorem card_ {r:Regime I}(g:Guide r n): gSlice n r where
  kn := g.generator n
  en := g.depth n
  mn := g.mod_ n
  shape:=funext (fun i=> by
    change Focn (n i)*altN (n i)=_
    rw [breadth (h i)]; exact (faces_shape (n i)).1.symm)
  pos i := (h i).face
  small i:=(faces_shape ..).2
  lock i:=(h i).safe.2.2
  range_ i:=fixRoom ..
  area i:=by
    change Focn (n i)*altN (n i)≤_
    rw [breadth (h i)]
    exact (face_margin _).2.trans ((digitRoom ..).trans (Nat.le_succ _))
end
end Bureau

end IntegerMultiplication
end Computability
end OAI
