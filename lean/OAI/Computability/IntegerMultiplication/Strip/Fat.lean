import OAI.Computability.IntegerMultiplication.Strip.Header

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {X : Type*}
-- record size height v, number of header/record pairs n (nonzero)
-- measure poly overhead per record even if not enough genuine width.
def mass (r : Regime X) (n l : X → ℕ) (k : ℕ) (x : X) : ℝ :=
  (n x:ℝ)*((l x:ℝ)+(r.scale x+1:ℝ)^k)

variable {r : Regime X} {n l : X→ℕ}
theorem unit_mass (h : ∀ x, n x ≥ 1) (k : ℕ) (x) : 1 ≤ mass r n l k x := by
  unfold mass
  have w0 : (1:ℝ) ≤ (r.scale x+1:ℝ)^k := one_le_pow₀ (by simp)
  exact (by norm_num : (1:ℝ) ≤ 1*1).trans (mul_le_mul (by exact_mod_cast h x) (by linarith [Nat.cast_nonneg (α:=ℝ) (l x)])
    (by norm_num) (by positivity))

theorem mass_le {k j : ℕ} (h : k≤j) (x : X) :
    mass r n l k x ≤ mass r n l j x := by unfold mass; gcongr; simp

def Rip (r : Regime X) (n l : X→ℕ) (q f : X→Tree) := ∃ k, Carries (mass r n l k) q f
namespace Rip
variable {q f g m x : X→Tree}
theorem chain (h : Rip r n l q f) (j : Rip r n l f g) : Rip r n l q g := by
  obtain ⟨a,h⟩ := h; obtain ⟨b,j⟩ := j
  exact ⟨a+b,(h.larger (mass_le (by omega : a≤a+b))).chain (j.larger (mass_le (by omega : b≤a+b)))⟩
theorem twice (h : Rip r n l q f) (j : Rip r n l q g) :
    Rip r n l q (together f g) := by
  obtain ⟨a,h⟩ := h; obtain ⟨b,j⟩ := j
  exact ⟨a+b,(h.larger (mass_le (by omega : a≤a+b))).twice (j.larger (mass_le (by omega : b≤a+b)))⟩

theorem header (pos : ∀ x, n x ≥ 1) {a : X→Tree} (h : Regime.Small r a) :
    Rip r n l r.header a := by
  obtain ⟨b,⟨k,C,u⟩,ht⟩ := h
  obtain ⟨m,N,g⟩ := r.gauge
  have pass {d : X→ℕ} {D i : ℕ} (e : ∀ x,d x ≤ D*(r.scale x+1)^i)
      (hi : i ≤ k+m) (x : X) :
      (d x : ℝ) ≤ (D:ℝ)*mass r n l (k+m) x := by
    calc
     _ ≤ ((D*(r.scale x+1)^i:ℕ):ℝ) := by exact_mod_cast e x
     _ ≤ (D:ℝ)*mass r n l i x := by
      unfold mass; push_cast
      gcongr; exact (le_add_of_nonneg_left (by positivity)).trans
        (le_mul_of_one_le_left (by positivity) (by exact_mod_cast pos x))
     _ ≤ _ := by gcongr; exact mass_le hi _
  refine ⟨k+m,⟨unit_mass pos _,b,ht,C+1,fun i => ?_⟩, N,pass g (by omega)⟩
  push_cast; linarith [pass u (by omega) i, unit_mass (r:=r) (l:=l) pos (k+m) i]

theorem designed (pos : ∀ x,n x≥1) {a : X→Tree} (h : r.Small a) (q : Rip r n l f r.header) :
    Rip r n l f a := q.chain (header pos h)

theorem idle (h : Rip r n l q f) : Rip r n l f f := by
  obtain ⟨k,h⟩ := h; exact ⟨k,Carries.idles h.budget h.out⟩
theorem again (h : Rip r n l q f) : Rip r n l q q := by
  obtain ⟨k,h⟩ := h; exact ⟨k,Carries.idles h.budget h.small⟩

theorem left (h : Rip r n l q f) (z : Rip r n l m g) :
    Rip r n l (together q g) (together f g) := by
  obtain ⟨a,i⟩ := h; obtain ⟨b,j⟩ := z
  exact ⟨a+b,(i.larger (mass_le (by omega : a≤a+b))).first
    (j.larger (mass_le (by omega : b≤a+b))).out⟩

theorem right (h : Rip r n l q f) (z : Rip r n l m g) :
    Rip r n l (together g q) (together g f) := by
  obtain ⟨a,i⟩ := h; obtain ⟨b,j⟩ := z
  exact ⟨a+b,(i.larger (mass_le (by omega : a≤a+b))).second
    (j.larger (mass_le (by omega : b≤a+b))).out⟩
theorem split (z : Rip r n l q (together f g)) : Rip r n l q f ∧ Rip r n l q g := by
  obtain ⟨k,h⟩ := z; have p := h.out
  exact ⟨⟨k,h.chain (Carries.dropRight h.budget (Volume.left p) (Volume.right p))⟩,
    ⟨k,h.chain (Carries.dropLeft h.budget (Volume.left p) (Volume.right p))⟩⟩
end Rip
end Strip

end IntegerMultiplication
end Computability
end OAI
