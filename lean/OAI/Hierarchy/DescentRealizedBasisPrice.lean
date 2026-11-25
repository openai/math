import OAI.Hierarchy.DescentPaidResetLayout
import OAI.Hierarchy.DescentMixingTrajectory

namespace OAI
/-! # Paying the reset charges for exactly the layout returned by the mixer -/

namespace Hierarchy.DescentColonies
open DescentGL DescentLinearLayouts DescentBaseVariance DescentBaseProfile
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

def inputLevels (b : V→ℕ) (v : V) := k-b v+1
def inputDepth (b : V→ℕ) (v : V) (q : Fin (inputLevels (k:=k) b v)) := b v+q.val
omit [Fintype V] [DecidableEq V] in
theorem inputFits (b : V→ℕ) (hk : ∀v,b v≤k) (v : V) (q : Fin (inputLevels (k:=k) b v)) :
    inputDepth b v q≤k := by have := q.isLt;have := hk v;simp only [inputDepth,inputLevels] at *;omega

def pairDepth (near : V→Finset V) (b : V→ℕ) (c : Contacts near) := max (b c.1) (b c.2.val)
omit [Fintype V] [DecidableEq V] in
theorem pairFits (near : V→Finset V) (b : V→ℕ) (hk : ∀v,b v≤k) (c : Contacts near) :
    pairDepth near b c≤k := max_le (hk _) (hk _)

def truePotential (near : V→Finset V) (f B K : ℕ) (weight : V→Block k→ℕ) (traffic : V→V→Block k→ℝ)
    (b : V→ℕ) (hk : ∀v,b v≤k) (μ : Layout k) : ℝ :=
  let scale := 2^f*B
  mixingPotential (inputLevels b) (inputDepth b) (inputFits b hk) (pairDepth near b) (pairFits near b hk)
    (fun v=>normalized weight scale v ∘ address k)
    (fun c i=>traffic c.1 c.2.val (address k i)/(scale:ℝ)) f B K μ

theorem paid_of_measured_potential (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    {Δ r f B K hops : ℕ} (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (hB : 0<B) (hK : 0<K)
    (weight : V→Block k→ℕ) (room : ∀v i,weight v i≤B) (traffic : V→V→Block k→ℝ)
    (inc : ∀v i,∑w∈near v,traffic v w i≤weight v i) (ε : ℝ) (ep : 0≤ε) (hh : 0<hops)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (b : V→ℕ) (hk : ∀v,b v≤k) (geom : BaseGeometry near Δ r f B K ε weight traffic b) (μ : Layout k)
    (measured : truePotential near f B K weight traffic b hk μ ≤
      ((2:ℝ)^f*B)*(∑v,(2:ℝ)^b v)*(8*resetTail f)+(K:ℝ)^2*(∑c : Contacts near,∑i,traffic c.1 c.2.val i)/2^f) :
    PaidResetLayout near Δ r f B K hops ε weight traffic b hk μ := by
  refine ⟨geom.bounds,geom.smooth,geom.span,geom.capacity,geom.hubs,?_⟩
  let scale := 2^f*B
  let keys := resetKeys near Δ f B K weight traffic b hk μ
  let s (e : Contacts near) := e.1
  let t (e : Contacts near) := e.2.val
  let unit (e : Contacts near) (i : Block k) := traffic (s e) (t e) i/(scale:ℝ)
  let trafficTotal := ∑c : Contacts near,∑i,traffic c.1 c.2.val i
  let mass := ∑v,∑i,(weight v i:ℝ)
  have hp : 0<(scale:ℝ) := by dsimp [scale];positivity
  have G := Nat.clog_pos (by decide : 1<2) (show 1<2*Δ by omega)
  have decay := (decay_parameters (by omega : 0<Δ)).1
  have ratio : Δ≤2^Nat.clog 2 (2*Δ) :=
    (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans (Nat.le_pow_clog (by decide) _)
  have deg (v : V) : (next (fun u z=>z∈near u) v).card≤Δ := by simpa [next] using degree v
  have exactBill := bad_mass_of_layout deg branch ratio (D:=32*Nat.clog 2 (2*Δ)) le_rfl (by omega)
    b hk (fun v w adj=>by have := geom.smooth w v ((sym v w).mp adj);omega)
    f B hB weight room geom.density K (by exact_mod_cast hK) s t unit μ
  have one : (scale:ℝ)*(∑p∈validBases b keys,baseValue b hk (normalized weight scale) μ p) ≤
      4*truePotential near f B K weight traffic b hk μ := exactBill
  have estimate : (scale:ℝ)*(∑p∈validBases b keys,baseValue b hk (normalized weight scale) μ p) ≤
      4*((scale:ℝ)*(∑v,(2:ℝ)^b v)*(8*resetTail f)+(K:ℝ)^2*trafficTotal/2^f) := by
    apply one.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,trafficTotal] using measured
  rw [scale_base_values weight hp] at estimate
  have hm : 0≤mass := by dsimp [mass];positivity
  have hc : trafficTotal≤ε+mass := (contact_mass near weight traffic inc).trans (le_add_of_nonneg_left ep)
  have absCost := bad_fraction (add_nonneg ep hm) geom.span hc (resetTail_nonneg f) estimate small
  have hr : (0:ℝ)<hops := by exact_mod_cast hh
  calc
    _ ≤ (hops:ℝ)*((1/(hops:ℝ))*(ε+mass)) := mul_le_mul_of_nonneg_left absCost hr.le
    _ = ε+mass := by rw [←mul_assoc,one_div,mul_inv_cancel₀ hr.ne',one_mul]
    _ = _ := rfl

end
end Hierarchy.DescentColonies

end OAI
