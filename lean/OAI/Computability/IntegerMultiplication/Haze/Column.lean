import OAI.Computability.IntegerMultiplication.Phase.Morning

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk IntegerMultiplication.Phase
open Finset

variable {J I W U : Type} [Fintype J] [DecidableEq J] [Fintype W]
local notation "θ" => Net.Motif.sigma
variable (d : Guild J W U θ) (R : Series W) {r : Regime I}
variable (k : I→ℕ) (e : (i:I)→Estate (dim J) (dim J ^ k i))
variable (a : r.Small fun i=> (e i).cert (k i))
variable (u : Dom r.scale fun i=> (e i).metres)

abbrev rate i := (e i).terrain.count
abbrev pkey i := (e i).keys
abbrev o i := Dusk.Grain (e i).shade
abbrev condition i := (e i).terrain
noncomputable section
abbrev hue i :=
  ((width (e i).tops (e i).foot:ℕ)+(1:ℝ))*((dim J:ℝ)^θ)^k i

include d
omit [DecidableEq J] in
theorem hue0 i : 1 ≤ hue k e i := by
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · unfold width; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) (e i).foot,Nat.cast_nonneg (α:=ℝ) (e i).tops]
  exact one_le_pow₀ (Real.one_le_rpow (by exact_mod_cast d.large.trans' (by decide : 1≤3)) Motif.sigma_range.1.le)

variable (b : I→ℕ)
variable (x : (i:I)→pkey k e i→Frame W (b i) (k i)→ o k e i)
variable {L : I→ℕ}
abbrev group i := skein W R (b i) (k i)
abbrev steam := orchid (condition k e) (group R k b) (fun i=> (e i).shade) x
abbrev fir (x : (i:I)→pkey k e i→Frame W (b i) (k i)→ o k e i) :=
  steam R k e b fun i=>runOn (pointed false) (x i)
include d a u
abbrev yoke (x y : I→Tree) :=
  Breeze (hue k e) r (rate k e) L x y

omit [DecidableEq J] [Fintype W] d a in
theorem cw0 :
    Dom r.scale fun i=>dim J^k i := by
  apply u.mono
  intro i
  have t := (e i).range
  have h : 1≤width (e i).tops (e i).foot := by unfold width; omega
  exact (Nat.le_mul_of_pos_right _ h).trans (by omega)

omit [DecidableEq J] [Fintype W] d a in
theorem aw0 : Dom r.scale fun i=> (e i).shade+1 := by apply u.mono; intro i; have := (e i).range; omega
/-- power group, input already on common frame. prep issue done separately. -/
theorem astern
    (m : ∀ i,(group R k b i).count*((e i).shade+1) ≤ L i + dim W^k i*((e i).shade+1))
    {p : I→Tree} (v : Rip r (rate k e) L p (together (fun i=> (e i).cert (k i)) (steam R k e b x))) :
    yoke k e (r:=r) (L:=L) p (fir R k e b x) := by
  let Z (i:I) : QuestP (dim J) (W:=W) := ⟨k i,e i,b i,x i⟩
  have z := obtainC d R
  obtain ⟨σ,t⟩ := z
  have wA := cw0 k e u
  have wB := aw0 k e u
  have wH : Dom r.scale fun i=> dim W^k i := Spindle.growth (dim W) _ k _ wA (d.large.trans' (by decide))
  obtain ⟨t₀,C,E⟩ :=
    ((wH.mul wB |>.mul (Dom.const _ 2)).add
      (((u.add (Dom.const _ 1)).pow σ).mul wH))
  have N := climate (J:=J) Z a (by have := d.large; omega)
  let F := hue k e
  have f := hue0 d k e
  have qT := t.along Z
  have h : Sized (runrate F r (rate k e) L t₀) (together (fun i=> (e i).cert (k i)) (steam R k e b x))
      (fir R k e b x) := by
    refine qT.adapts (fun i=>one_le_mul_of_one_le_of_one_le (unit_mass N.1 t₀ i) (f i)) (C+2) (fun i => ?_)
    change pullout σ (Z i)*F i ≤ _*((rate k e i *(L i+(r.scale i+1:ℝ)^t₀)) * F i)
    rw [← mul_assoc ((C+2:ℕ):ℝ)]
    apply mul_le_mul_of_nonneg_right _ (le_trans (by norm_num) (f i))
    rw [mul_left_comm ((C+2:ℕ):ℝ)]
    apply mul_le_mul_of_nonneg_left _
      (show (0:ℝ)≤rate k e i by positivity)
    suffices h : (2*(b i*(dim W)^k i)*((e i).shade+1)+((e i).metres+1)^σ*(dim W)^k i:ℕ) ≤
        (C+2)*(L i + (r.scale i+1)^t₀) by
      dsimp only [timeMark,users,Z]
      have c : ((b i*dim W^k i*(2*((e i).shade+1)) + ((e i).metres+1)^σ * (dim W)^k i:ℕ)) ≤ _ :=
        (by nlinarith [h] : b i*dim W^k i*(2*((e i).shade+1)) + ((e i).metres+1)^σ * (dim W)^k i ≤ (C+2)*(L i + (r.scale i+1)^t₀))
      exact_mod_cast c
    have s := m i
    rw [group,strands] at s
    have u0 := E i
    change dim W^k i*((e i).shade+1)*2 + ((e i).metres+1)^σ*dim W^k i ≤ _ at u0
    unfold dim at *; nlinarith [Nat.zero_le (C*L i), Nat.zero_le ((r.scale i+1)^t₀)]
  obtain ⟨n,g⟩ := v
  let S := runrate F r (rate k e) L (n+t₀)
  exact ⟨f,n+t₀,(g.larger (d:=S) (fun i => (mass_le (r:=r) (by omega : n≤n+t₀) i).trans
    (le_mul_of_one_le_right (by unfold mass; positivity) (f i)))).sequence
      (h.mono fun i=> rate_higher i (f i) (by omega))⟩
end
end Haze

end IntegerMultiplication
end Computability
end OAI
