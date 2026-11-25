import OAI.Computability.IntegerMultiplication.Strip.Breeze

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Code Strip Adic Loom Net
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] {p : ℕ} [NeZero p]
variable {discount : ℝ} {r : Regime I} (k : I→ℕ) (s : (i:I)→Stair (dim J) p (k i))
variable (R : Series W) (d : Design J W L p discount)
variable {A : I→Type} (t : (i:I)→Series (A i))
noncomputable section

abbrev Key i := SpanKey (s i).north (s i).isle (s i).south (Block p (dim J ^ k i))
variable {l : I→ℕ}
abbrev src i := stock p (s i).north (s i).isle (s i).south (dim J^k i)
abbrev headcount i := (src k s i).count
variable (c : I→ℕ)
abbrev unitCell (i : I) := Frame W (c i) (k i)
abbrev packed (v : (i:I)→Key k s i→unitCell (W:=W) k c i→Bead) :=
  stackRun (src k s) fun i x => strip (skein W R (c i) (k i)) (v i x)
def gust (m : ℕ) (τ : ℝ) (i : I) := ((m:ℝ)^τ)^(k i)
theorem mild (m : ℕ) (z : 1≤ m) (h : 0≤discount) (i : I) :
    1 ≤ gust k m discount i :=
  one_le_pow₀ (Real.one_le_rpow (by exact_mod_cast z) h)

include d
theorem Loft
    (w : (i:I)→Key k s i→unitCell (W:=W) k c i→Bead)
    (minSize : ∀ i,c i*dim W^k i ≤ l i + dim W^k i)
    (controls : r.Small fun i => (s i).ticket)
    (localSize : Dom r.scale (fun i => dim W^k i))
    (filterSize : Dom r.scale (fun i => (s i).supplyLimit))
    (h : 0≤discount)
    {u : I→Tree}
    (input : Rip r (headcount k s) l u (together (fun i => (s i).ticket) (packed k s R c w))) :
    Breeze (gust k (dim J) discount) r (headcount k s) l u
      (packed k s R c (fun i => w i ∘ swapper _ _ _)) := by
  obtain ⟨m,a⟩ := accelerate R d h
  let G (i:I) : Where (dim J) p W := ⟨k i,s i,c i,w i⟩
  have e : Sized (fare discount m ∘ G)
      (together (fun i => (s i).ticket) (packed k s R c w))
      (packed k s R c (fun i => w i ∘ swapper _ _ _)) := a.along G
  obtain ⟨j,t⟩ := input
  have h0 := mild k (dim J) (le_trans (by omega) d.occupancy) h
  have tn : ∀ i,1 ≤ headcount k s i := (Where.station_t G d.large controls).1
  obtain ⟨b,y,T⟩ := localSize.add
    (((filterSize.add (Dom.const _ 1)).pow m).mul localSize)
  -- adapt fare. runrate multiply factor.
  have adapt : Sized (runrate (gust k (dim J) discount) r (headcount k s) l b)
      (together (fun i => (s i).ticket) (packed k s R c w)) (packed k s R c (fun i => w i ∘ swapper _ _ _)) := by
    refine e.adapts (fun i => one_le_mul_of_one_le_of_one_le (unit_mass tn b i) (h0 i)) (y+1) ?_
    intro i
    change (↑(headcount k s i) * ((timeNow (G i) : ℝ) + ((s i).supplyLimit+1:ℝ)^m*(dim W:ℝ)^k i)) * gust k (dim J) discount i ≤ ↑(y+1:ℕ)*(mass r (headcount k s) l b i * gust k (dim J) discount i)
    specialize T i; have hg := h0 i
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    let T0 := headcount k s i
    unfold mass
    rw [← mul_assoc]
    rw [mul_comm ((y+1:ℕ):ℝ) (↑(headcount k s i)),mul_assoc] -- cast order
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    specialize minSize i
    simp only [timeNow,G] at *
    have u : ((c i * dim W^k i:ℕ):ℝ) ≤ (l i:ℝ)+(dim W:ℝ)^k i := by exact_mod_cast minSize
    have v : (((dim W)^k i:ℕ):ℝ) +
        ((↑(s i).supplyLimit+1:ℝ)^m)*((dim W:ℝ)^k i) ≤ (y:ℝ)*(r.scale i+1:ℝ)^b := by exact_mod_cast T
    push_cast at *
    nlinarith [Nat.cast_nonneg (α:=ℝ) (l i),pow_nonneg (by positivity : (0:ℝ)≤r.scale i+1) b]
  have L := t.larger (d:= runrate (gust k (dim J) discount) r (headcount k s) l (b+j))
    (fun i => (mass_le (l:=l) (r:=r) (n:=headcount k s) (by omega : j≤b+j) i).trans
      (le_mul_of_one_le_right (le_trans (by norm_num) (unit_mass tn _ i)) (h0 i)))
  exact ⟨h0,b+j,L.sequence (adapt.mono fun i => rate_higher i (h0 _) (by omega))⟩
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
