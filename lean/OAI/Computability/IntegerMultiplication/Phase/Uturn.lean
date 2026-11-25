import OAI.Computability.IntegerMultiplication.Phase.Frontier

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset Matrix
variable {I J O T R : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (l : Lens O (Addr J) T) (c : Quarter R)
def mag (x : Addr J) := (2:Clock)*weight x

theorem raize (x : O→R) (u) :
    operate l (Matrix.diagonal (swapSignVec (fun _ : J=>true))) x u =
    c.ph (mag (l u).1)*x u := by
  rw [Strip.Optic.diag]
  unfold mag Walsh.weight swapSignVec
  simp only [Finset.mul_sum,c.of_sum,ite_true]
  congr 2
  funext i
  exact (c.shift _).symm

theorem switched (x : O→R) (u) :
    c.ph ((dim J:Clock)*(-1)+mag (l u).1) *
    operate l (allC c (fun _=>false))
      (fun i=> c.ph (mag (l i).1)*x i) u = operate l (allC c (fun _=>true)) x u := by
  have t (x : O→R) : (fun i=> c.ph (mag (l i).1)*x i) = operate l (Matrix.diagonal (swapSignVec (fun _ => true))) x :=
    funext fun i=> (raize l c x i).symm
  rw [c.of_add,← ph_pow, mul_assoc, t]
  rw [← raize]
  rw [← unwrap c,Strip.Optic.scale,Strip.Optic.dot,Strip.Optic.dot,
    c.back]
  simp only [Finset.prod_const,Finset.card_univ,Pi.smul_apply,smul_eq_mul,dim]

-- shared C
noncomputable abbrev pointed {p v : Tape} {h g n : ℕ} {w : ℕ}
    (b : Bool)
    (x : Base p v (Screen h g (Fin n))→Grain w) :=
  operate (target p v h g (Fin n)) (allC (gaunt w) (fun _=>b)) x

noncomputable section
variable {Q : Type} {r : Regime I} {z : Job Q} {Y : I→Q→Prop}
variable {f : I→ℝ} (p v : I→Tape) (h g n w : I→ℕ)
variable {S : I→ Type} (s : (i:I)→Series (S i)) (L : I→ℕ)
variable (hp : Told r p) (hv : Told r v) (q : r.Has (tally ∘ extent h g n))
    (d : r.Has fun i => signs (h i) (g i) (n i))

abbrev state (i:I) := Base (p i) (v i) (Screen (h i) (g i) (Fin (n i+1)))
abbrev throng i := plain (p i) (v i) (h i) (g i) (n i+1)
abbrev bunch := orchid (throng p v h g n) s w
def runOn {A X : Type} (m : (A→R)→(A→R)) (x : A→X→R) : A→X→R :=
  fun a b=>m (fun a=>x a b) a
abbrev transfer (b : Bool) (x : (i:I)→state p v h g n i→S i→Grain (w i)) :=
  fun (i:I)=> runOn (pointed b) (x i)
abbrev DriveC (z₁ : I→ℕ) (b : Bool) := ∀ x,
    Quarterback z f r z₁ L Y 1 (orchid (throng p v h g n) s w x)
      (orchid (throng p v h g n) s w (transfer p v h g n w b x))

include hp hv q d
theorem walter
    (t : DriveC p v h g n w s L (fun i=>(throng p v h g n i).count) false (z:=z) (f:=f) (r:=r) (Y:=Y))
    (m : ∀ i,(s i).count*(w i+1)≤L i) :
    DriveC p v h g n w s L (fun i=>(throng p v h g n i).count) true (z:=z) (f:=f) (r:=r) (Y:=Y) := by
  let α := state p v h g n
  let A := throng p v h g n
  let T i := target (p i) (v i) (h i) (g i) (Fin (n i+1))
  have C : wish (r:=r) A (fun i a=> pin a.2.1) := glow p v h g n hp hv q d
  let u (i:I) (a : α i) := mag ((T i a).1)
  have U : wish (r:=r) A u := w_lens A _ C (2*·)
  let v₂ i := (dim (Fin (n i+1)) : Clock)*(-1)
  have e : r.Has v₂ := by
    have a := (d.ez (Easy.snd.compose Easy.snd)).ez easy_time
    have e := a.ez (Easy.finite (fun i:Clock=> (i+1)*(-1)))
    simpa [signs,v₂,dim] using e
  have V := w_arg A C.valid v₂ e
  intro x
  let x₁ (i:I) (a:α i) b := (gaunt (w i)).ph (u i a)*x i a b
  have X := t x₁
  let B := bunch p v h g n w s
  have h₁ := Year.fr (j:=z) (y:=Y) (forth A s x u U m) X.safer
  let x₂ := transfer p v h g n w false x₁
  let u₂ := fun i a => v₂ i+u i a
  let x₃ (i:I) (a:α i) b := (gaunt (w i)).ph (u₂ i a)*x₂ i a b
  have h₂ := Year.fr (j:=z) (y:=Y) (forth A s x₂ u₂ (w_add A (fun i _=> v₂ i) u V U) m) X.safer
  have k : Quarterback z f r (fun i=>(A i).count) L Y 1 (B x) (B x₃) := by
    have h₀ (x) := shelter A s w x C.valid m
    simpa only [zero_add,add_zero] using
      ((Quarterback.run h₁ X C.valid.1 (h₀ _) (h₀ _)) |> fun p=>
        Quarterback.run p h₂ C.valid.1 (h₀ _) (h₀ _))
  have g : x₃ = transfer p v h g n w true x := by
    funext i a b
    exact switched (T i) (gaunt (w i)) (fun a=>x i a b) a
  rw [g] at k
  exact k
end
end Phase

end IntegerMultiplication
end Computability
end OAI
