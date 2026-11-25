import OAI.Computability.IntegerMultiplication.Phase.Hammer

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset
variable {J W U I Q : Type} {σ : ℝ}
variable [Fintype J] [DecidableEq J] [Fintype W]
variable {r : Regime I} {z : Job Q} {Y : I→Q→Prop}
variable (p v : I→Tape) (h g e w : I→ℕ)
variable {S : I→ Type} (s : (i:I)→Series (S i)) (L : I→ℕ)
variable (hp : Told r p) (hv : Told r v)

-- variant over F>0 instead of F+1, and regroup via bright
abbrev dect (i:I) := e i * width (h i) (g i)
def safe (f K : ℕ) : Prop := (3*(f*K)+1)*(32*(f-1)) ≤ 2^K
theorem safe_r {f k K} (h : k≤f) (t : safe f K) : safe k K := by
  refine le_trans (b:=((3*(f*K)+1)*(32*(f-1)))) ?_ t
  gcongr

noncomputable section
abbrev white := Spindle.modes (τ:=Motif.sigma) (dect h g e)
variable (m₀ : ∀ i,1≤e i) (ρ : r.Has (tally ∘ dect h g e))
variable (j0 : r.Has fun i=> signs (h i) (g i) (e i-1))
variable (m : ∀ i,(s i).count*(2*(w i+1))≤L i)
variable (guide : Guild J W U σ)
variable (c : ∀ i a,a∈p i ++ v i → a≤base)
variable (u : ∀ i,safe (e i) (width (h i) (g i)))

abbrev land (i:I) (b : ℕ) := Adic.field 2 (b*width (h i) (g i))
abbrev north (j:J) (i:I) := p i++leftF guide.order (land h g i (e i)) j
abbrev south (j:J) (i:I) := rightF guide.order (land h g i (e i)) j++v i

abbrev sky i := Base (p i) (v i) (Screen (h i) (g i) (Fin (e i)))
abbrev night i := plain (p i) (v i) (h i) (g i) (e i)
abbrev press := orchid (night p v h g e) s w
abbrev viewOn (x : (i:I)→ sky p v h g e i → S i→Grain (w i)) :=
  fun i=> runOn (pointed false) (x i)
abbrev Lesson (k : ℕ) :=
  ∀ x : (i:I)→sky p v h g e i → S i→Grain (w i),
      Quarterback z (white h g e) r (fun i=>(night p v h g e i).count) L Y k
        (press p v h g e w s x) (press p v h g e w s (viewOn p v h g e w x))
abbrev subroutine := ∀ j : J, Lesson (north p h g e guide j) (south v h g e guide j)
  h g e w s L 1 (z:=z) (Y:=Y) (r:=r)

def zI (i:I) : ℕ := e i*dim J
include m₀
omit m₀
private theorem succ_f (e : I→ℕ) (h : ∀ i,1≤e i) :
    ∃ n : I → ℕ, e=fun i=> n i+1 :=
  ⟨fun i=>e i-1,funext fun i=> by specialize h i; dsimp; omega⟩

include m₀ hp hv ρ j0 m guide c u
private theorem final_r (t : subroutine p v h g e w s L guide (z:=z) (Y:=Y) (r:=r))
    (R : Series W) (x : (i:I)→Panels (p i) (v i) (h i) (g i) J (e i)→ S i× W→Grain (w i))
    (u0 : Alive r (fun i=>(front (p i) (v i) (h i) (g i) (e i) guide.order).count) L
      (orchid (fun i=>front (p i) (v i) (h i) (g i) (e i) guide.order) (double_ s R) w x)) :
    let N := fun i=>front (p i) (v i) (h i) (g i) (e i) guide.order
    Quarterback z (white h g e) r (fun i=>(N i).count) L Y
      (charges guide) (orchid N (double_ s R) w x)
        (orchid N (double_ s R) w (fun i=> runOn (pipe (joint ..)
          (allC (gaunt (w i)) (fun (_:J)=>false))) (x i))) := by
  obtain ⟨n,E⟩ := succ_f _ m₀
  subst e
  exact clang p v h g n w s L hp hv ρ (by simpa using j0) m guide c (by simpa [safe] using u) (fun j V=>t j V)
    R x u0

abbrev taller {m : ℕ} (_f : J≃Fin m) i :=
  plain (p i) (v i) (h i) (g i) (e i*m)
abbrev boot (x : (i:I) → Base (p i) (v i) (Screen (h i) (g i) (Fin (zI (J:=J) e i))) →
    S i×W→Grain (w i)) := fun i => x i ∘ (bright (h i) (g i) (e i) (p i) (v i) guide.order).cast
/-- procedure for a positive group of slot width e (whole engine) -/
theorem start_r (t : subroutine p v h g e w s L guide (z:=z) (Y:=Y) (r:=r))
    (R : Series W)
    (x : (i:I) → Base (p i) (v i) (Screen (h i) (g i) (Fin (zI (J:=J) e i))) →
      S i×W→Grain (w i))
    (u0 : Alive r (fun i=>(taller p v h g e guide.order i).count) L
      (orchid (taller p v h g e guide.order) (double_ s R) w x)) :
    Quarterback z (white h g e) r (fun i=>(taller p v h g e guide.order i).count) L Y
      (charges guide) (orchid (taller p v h g e guide.order) (double_ s R) w x)
        (orchid (taller p v h g e guide.order) (double_ s R) w
          (fun i=>runOn (pointed false) (x i))) := by
  let s0 := taller p v h g e guide.order
  let N := fun i=> front (p i) (v i) (h i) (g i) (e i) guide.order
  let T (i:I) : Adopt (N i) (s0 i) := bright (h i) (g i) (e i) (p i) (v i) guide.order
  have u1 (i:I) : (N i).count=(s0 i).count := (T i).cost
  change Quarterback z _ _ (fun i=>(s0 i).count) L Y _ _ _
  have e0 (x) : orchid s0 (double_ s R) w x=orchid N (double_ s R) w (fun i=>x i ∘ (T i).cast) :=
    funext fun i=> (T i).packet _
  let y := fun (i:I)=> x i ∘ (T i).cast
  have uN : Alive r (fun i=> (N i).count) L (orchid N (double_ s R) w y) := by
    change Alive r _ _ (orchid _ _ _ (fun i=> x i ∘ _))
    erw [← e0 x]
    simp_rw [u1]; exact u0
  have V₀ := final_r p v h g e w s L hp hv m₀ ρ j0 m guide c u t R _ uN
  have eq : (fun i=> runOn (pipe (joint (p i) (v i) (h i) (g i) J (e i))
          (allC (gaunt (w i)) (fun (_:J)=>false))) (y i)) =
      fun (i:I)=> runOn (pointed false) (x i) ∘ (T i).cast := by
    funext i a b
    exact congrFun (combination (h i) (g i) (e i) (p i) (v i) guide.order
      (gaunt (w i)) (fun a=> x i a b)).symm a
  change Quarterback z _ _ _ _ _ _ _ (orchid N (double_ s R) w _) at V₀
  rw [eq] at V₀
  erw [← e0 (fun i=>runOn (pointed false) (x i))] at V₀
  change Quarterback z _ _ (fun i=> (N i).count) _ _ _ _ _ at V₀
  simp_rw [u1] at V₀
  change Quarterback z _ _ (fun i=>(s0 i).count) L _ _ (orchid s0 _ _ _) (orchid s0 _ _ _)
  rw [e0 x]
  exact V₀
end
end Phase

end IntegerMultiplication
end Computability
end OAI
