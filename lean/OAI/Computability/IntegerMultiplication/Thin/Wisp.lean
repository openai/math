import OAI.Computability.IntegerMultiplication.Thin.Exchange
import OAI.Computability.IntegerMultiplication.Loom.Arrivals

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Strip Dims Loom Code
variable {I X : Type} (r : Regime I) (N:I→ℕ)
abbrev single (_i:I) : ℕ := 1
abbrev seat (k:ℕ) := mass r single N k
abbrev Deck (p q : I→Tree) := Rip r single N p q
abbrev Live (p : I→Tree) := Deck r N p p
abbrev Baggage {A:I→Type} (z:I→Tree) (s:(i:I)→Series (A i)) :=
  Deck r N z (fun i => send (tally (s i).count))
theorem little (k:ℕ) (i:I) : (N i:ℝ)+1 ≤ seat r N k i := by
  unfold seat mass single
  push_cast
  simpa using one_le_pow₀  (show 1 ≤ (r.scale i:ℝ)+1 by simp) (n:=k)
-- variable implicit r
variable {r N} {z:I→Tree}
theorem bags {s : I→Tape} (p : Told r s)
    (h : Deck r N z r.header) (k : ∀ i, Dims.room (s i) ≤ N i) :
    Baggage r N z (fun i=>layout (s i)) := by
  simp only [Baggage,Dims.space]
  apply h.chain (Rip.relay (r:=r) (n:=single) (l:=N) (fun _=> Nat.le_refl _) _
    (Rip.header (fun _=>Nat.le_refl _) p.shape) (Dims.unary.on (fun i:I => ⟨s i,p.solid i⟩)) ?_)
  refine ⟨0,1,fun i=> ?_⟩
  simp only [mass,single] -- goal u i val subtype
  push_cast
  simpa using k i

theorem surveyed {A : I → Type} (s:(i:I)→Series (A i)) (x:(i:I)→A i→Tree)
    (K:ℕ) (l : I→ℕ) (e : ∀ i,(s i).count*(l i+1)≤N i)
    (h : ∀ i a,(x i a).count≤K*(l i+1)) :
    Live r N (stackRun s x) := by
  refine ⟨0,Carries.idles (unit_mass (fun (_:I)=> Nat.le_refl 1) _)
    ⟨K+1,fun i=>?_⟩⟩
  apply le_trans _ (mul_le_mul_of_nonneg_left (little r N _ _) (by positivity : (0:ℝ) ≤ ↑(K+1 : ℕ)))
  have b (i) := stripe_size (s i) (x i) _ (h i)
  specialize e i
  exact_mod_cast (show (stripe (s i) _).count ≤ (K+1)*(N i+1) from (b i).trans (by nlinarith [Nat.le_mul_of_pos_right ((s i).count) (Nat.succ_pos (l i))]))

variable {P G B : I→Type} {p:(i:I)→Series (P i)} {g:(i:I)→Series (G i)} {b:(i:I)→Series (B i)}
variable (a:Series X)
variable (h : Baggage r N z p) (d : Baggage r N z g) (e : Baggage r N z b)
variable (t : ∀ i,((p @@ g @@ b) i).count ≤ N i) (v : 1≤a.count)
variable (p0 : ∀ i,1≤(p i).count) (b0 : ∀ i, 1≤(b i).count) (g0 : ∀ i,1≤(g i).count)
include h d e t v p0 b0 g0
theorem twist (x : (i:I)→ P i × X × G i × X × B i→Tree)
    (u : Deck r N z (stackRun (p @@ sr a @@ g @@ sr a @@ b) x)) :
    Deck r N z (stackRun (p @@ sr a @@ g @@ sr a @@ b)
      (fun i j=> x i (j.1,j.2.2.2.1,j.2.2.1,j.2.1,j.2.2.2.2))) := by
  obtain ⟨k₁,h⟩ := h
  obtain ⟨k₂,d⟩ := d
  obtain ⟨k₃,e⟩ := e
  obtain ⟨k₄,u⟩ := u
  let k := k₁+k₂+k₃+k₄
  have law {s t} {l} (h:Carries (seat r N l) s t) (v:l≤k) := h.larger (mass_le v)
  refine ⟨k, skew p g b a v ⟨law h (by omega : k₁≤k),p0⟩ ⟨law d (by omega : k₂≤k),g0⟩
    ⟨law e (by omega : k₃≤k),b0⟩ ?_ _ (law u (by omega : k₄≤k))⟩
  refine ⟨1,fun i=>?_⟩
  have v := t i
  have e := little r N k i
  simp only [Nat.cast_one,one_mul]
  exact (show (((p @@ g @@ b) i).count:ℝ) ≤ (N i:ℝ)+1 by
    exact_mod_cast (le_trans v (Nat.le_succ _))).trans e
end Thin

end IntegerMultiplication
end Computability
end OAI
