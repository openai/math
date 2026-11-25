import OAI.Computability.IntegerMultiplication.Strip.Fat
import OAI.Computability.IntegerMultiplication.Strip.Bearing

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I X : Type}

def Regime.pull (r : Regime I) (f : X→I) : Regime X :=
  ⟨fun x => r.scale (f x), fun x => r.header (f x), r.gauge.map f⟩
theorem Rip.pull {r : Regime I} {n h : I→ℕ} {p m : I→Tree}
    (e : Rip r n h p m) (f : X→I) :
    Rip (r.pull f) (fun x => n (f x)) (fun x => h (f x)) (fun x => p (f x)) (fun x => m (f x)) := by
  obtain ⟨k,t⟩ := e
  exact ⟨k,t.slide f⟩
variable {r : Regime I} {n l : I → ℕ}
variable (no : ∀ x, 1≤n x)

include no in
theorem Rip.relay {X : Type*} {input a : I→Tree} [Codec X] (f : I→X)
    (p : Rip r n l input (fun i => send (f i))) {u : I→ℕ}
    (s : Code.Task u (send ∘ f) a)
    (h : ∃ k D : ℕ, ∀ i,(u i : ℝ)+1 ≤ (D:ℝ)*mass r n l k i) :
    Rip r n l input a := by
  obtain ⟨k,q⟩ := p
  obtain ⟨j,D,e⟩ := h
  exact ⟨k+j,(q.larger (mass_le (by omega : k≤k+j))).sequence
    ((show Sized _ _ _ from ⟨unit_mass no j,u,s,D,e⟩).mono (mass_le (by omega : j≤k+j)))⟩

/- Generate a tally giving length in records of dynamic digit shape from authorized small shape. -/
include no in
theorem Rip.ruler {s : I → Dims.Tape} (p : r.Has (Dims.shape ∘ s)) (q : ∀ i,Dims.solid (s i))
    (h : ∀ i, Dims.room (s i) ≤ n i) :
    Rip r n l r.header (send ∘ tally ∘ Dims.room ∘ s) := by
  apply Rip.relay no _ (Rip.header no p) (Dims.unary.on (fun i => ⟨s i, q i⟩))
  refine ⟨0,2,fun i => ?_⟩
  have ps : (Dims.room (s i):ℝ) ≤ n i := by exact_mod_cast h i
  have np : (1:ℝ) ≤ n i := by exact_mod_cast no i
  simp [mass]
  have hh : 0≤(n i:ℝ)*(l i) := by positivity
  nlinarith

-- variant carve + lift. No masks version fan. Need bounds convert.
theorem Rip.carve {P B : I → Type} (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
    (v : (i:I)→P i × B i→Tree) {p : I→Tree}
    (g : Rip r n l p (fun i => rulers (s i) (t i)))
    (dataR : Rip r n l p (stackRun (fun i => (s i).cart (t i)) v))
    (ps : ∀ i, 1≤(s i).count) (pt : ∀ i,1≤(t i).count)
    (overall : ∀ i,(s i).count*(t i).count ≤ n i) :
    Rip r n l p (stackRun s fun i a => stripe (t i) fun b => v i (a,b)) := by
  obtain ⟨a,j⟩ := g; obtain ⟨b,k⟩ := dataR
  have e := mass_le (r:=r) (n:=n) (l:=l) (by omega : a≤a+b)
  have f := mass_le (r:=r) (n:=n) (l:=l) (by omega : b≤a+b)
  refine ⟨a+b, IntegerMultiplication.Strip.carve _ _ _ (k.larger f) (j.larger e) ⟨4,fun i => ?_⟩⟩
  have g : ((s i).count:ℝ)*(t i).count ≤ n i := by exact_mod_cast overall i
  have pa : (1:ℝ)≤(s i).count := by exact_mod_cast ps i
  have pb : (1:ℝ)≤(t i).count := by exact_mod_cast pt i
  have t0 : (1:ℝ) ≤ ((r.scale i+1:ℝ)^(a+b)) := one_le_pow₀ (by simp)
  calc
   _ ≤ (2:ℝ)*(s i).count*(2*(t i).count) := by gcongr <;> linarith
   _ = (4:ℝ)*((s i).count*(t i).count:ℝ) := by ring
   _ ≤ ((4:ℕ):ℝ)*mass r n l (a+b) i := by
    norm_num
    exact g.trans (le_mul_of_one_le_right (by positivity) (t0.trans (le_add_of_nonneg_left (by positivity))))

theorem Rip.flatten {P B : I→Type} (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
    (v : (i:I)→P i × B i→Tree) {p : I→Tree}
    (g : Rip r n l p (stackRun s fun i a => stripe (t i) fun b => v i (a,b))) :
    Rip r n l p (stackRun (fun i => (s i).cart (t i)) v) := by
  obtain ⟨a,h⟩ := g
  exact ⟨a, IntegerMultiplication.Strip.flatten s t v h⟩

/-- coarse lifting to grouped records. -/
theorem Rip.apply {P B : I → Type} (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
    (v u : (i:I)→P i × B i→Tree) {p : I→Tree}
    (b : Rip (r.pull (Sigma.fst : Sigma P → I)) (fun i => (t i.1).count) (fun i => l i.1)
      (fun i => stripe (t i.1) fun x => v i.1 (i.2,x)) (fun i => stripe (t i.1) fun x => u i.1 (i.2,x)))
    (h : Rip r n l p (stackRun s fun i a => stripe (t i) fun b => v i (a,b)))
    (overall : ∀ i,(s i).count*(t i).count ≤ n i) :
    Rip r n l p (stackRun s fun i a => stripe (t i) fun b => u i (a,b)) := by
  obtain ⟨a,b⟩ := b
  apply h.chain
  have g := liftoff s (fun i x => stripe (t i) fun c => v i (x,c))
    (fun i x => stripe (t i) fun c => u i (x,c)) (mass r (fun i => (t i).count) l a) b
  obtain ⟨e,j⟩ := h
  refine ⟨e+a,g.times (j.larger (mass_le (by omega : e≤e+a))).budget 2 (fun i => ?_)⟩
  have hv := (j.larger (mass_le (by omega : e≤e+a))).budget i
  suffices hh : ((s i).count: ℝ)*mass r (fun i => (t i).count) l a i ≤ mass r n l (e+a) i by
    norm_num; linarith
  calc
   _ ≤ mass r n l a i := by
    unfold mass
    rw [← mul_assoc]
    gcongr
    exact_mod_cast overall i
   _ ≤ _ := mass_le (by omega) i

-- generalized B' and arbitrary packs sometime
end Strip

end IntegerMultiplication
end Computability
end OAI
