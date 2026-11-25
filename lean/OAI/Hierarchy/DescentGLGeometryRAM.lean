import OAI.Hierarchy.DescentGLPhysicalTrajectory
import OAI.Hierarchy.DescentMixingIntegerWeights

namespace OAI
/-! # The physically published mixing map satisfies the joint geometric estimate -/

namespace Hierarchy.DescentGL.PhysicalTrajectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentIntegerScale DescentWalshTables DescentBaseVariance
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {A C : Type*} [Fintype A] [Fintype C] {w bits F B K base : ℕ}
variable (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (hj : ∀ a s,j a s≤bits)
    (cj : C→ℕ) (hcj : ∀c,cj c≤bits) (x : A→Bits bits→ℕ) (y : C→Bits bits→ℕ)
local notation "q" => (2^F*B)
local notation "loads" => (fun a i=>(x a i:ℝ)/(q:ℝ))
local notation "flow" => (fun c i=>(y c i:ℝ)/(q:ℝ))
local notation "W" => mixingWeightNumerator levels j cj x y F B K

theorem physical_mixing_layout (bank : ℕ→ℕ) (m : Memory w) (room : Room w bits base bank)
    (initial : Layout bits) (hB : 0<B) (n : A→ℝ) (X : ℝ)
    (count : ∀ a (s : Fin (levels a)),(2:ℝ)^(j a s)=n a*2^s.val) (hn : ∀a,0<n a)
    (small : ∀a i,loads a i≤1/(2:ℝ)^F) (mass : ∀a,∑i,loads a i≤n a)
    (thin : ∀c i,flow c i≤1/(2:ℝ)^F) (quota : (∑c,∑i,flow c i)≤X/((2:ℝ)^F*B))
    (scaleBits countBits weightBits massBits : ℕ) (scale : q≤2^scaleBits)
    (members : (∑a,levels a)+Fintype.card C≤2^countBits)
    (levelWeight : ∀a (s : Fin (levels a)),4*2^((s.val+7)/8)≤2^weightBits) (rate : K^2≤2^weightBits)
    (loadBits : ∀a,(∑i,x a i)≤2^massBits) (flowBits : ∀c,(∑i,y c i)≤2^massBits)
    (fits : 3*bits+(scaleBits+countBits+weightBits+2*massBits)+2≤w)
    (physical : ∀l (d : Fin (2^bits)),m (bank l.val+d.val)=(W l (DescentGLScoreRAM.vec d):Word w)) :
    let out := finalMemory bits base bank m
    let r := (2:ℝ)^(1/8:ℝ)
    (program w bits base bank).Exec m out (time bits base bank bits+DescentGLPermutationRAM.clock bits) ∧
    ∃ μ : Layout bits, mixingPotential levels j hj cj hcj loads flow F B K μ ≤
      ((2:ℝ)^F*B)*(∑a,n a)*(8*((2:ℝ)^F)^(-(7/8):ℝ)*(1/(r-1)+1/(1-r/2)))+(K:ℝ)^2*X/2^F ∧
      (∀i : Fin bits,out (pointer bits base i.val)=((rowIndex bits (rowFunctional μ i)).val:Word w)) ∧
      (∀d : Fin (2^bits),out (outputBase bits base+d.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm d))).val:Word w)) ∧ ∀a<base,out a=m a := by
  have pos : 0<q := Nat.mul_pos (Nat.two_pow_pos _) hB
  obtain ⟨run,_,steps,upper⟩ := chosen_mixing_layout bits F levels j hj cj hcj loads n flow B K X
    (by exact_mod_cast hB) count hn (by intros; positivity) small mass (by intros; positivity) thin quota initial
  have weightEq : mixingCollisionWeights levels j hj cj hcj loads flow F B K=Weights W q := by
    funext l d
    simpa only [Weights, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mixingCollisionWeights_eq_integer levels j hj cj hcj x y F B K l d
  have choices : Chooses run (Weights W q) := by
    rw [←weightEq]
    exact fun i=>⟨(steps i).1,(steps i).2.1⟩
  exact ⟨exec bank m room,run bits,upper,
    receipt bank W run choices m room pos fits
      (fun l d=>mixingWeightNumerator_bound levels j cj x y F B K l d _ _ _ _ scale members levelWeight rate loadBits flowBits)
      physical⟩

end
end Hierarchy.DescentGL.PhysicalTrajectory

end OAI
