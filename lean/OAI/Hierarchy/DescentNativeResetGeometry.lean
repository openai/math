import OAI.Hierarchy.DescentGLGeometryRAM
import OAI.Hierarchy.DescentRealizedBasisPrice
import OAI.Hierarchy.DescentMeasuredBaseGeometry

namespace OAI
/-! # The actual native GL permutation pays the marked load on its own physical geometry -/

namespace Hierarchy.DescentColonies
open DescentGL DescentLinearLayouts DescentBaseVariance DescentIntegerScale DescentBaseProfile
open DescentGL.PhysicalTrajectory Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k w base : ℕ}
variable (near : V→Finset V) {Δ f B K r hops : ℕ} (weight : V→Block k→ℕ) (flow : V→V→Block k→ℕ)
variable (b : V→ℕ) (hk : ∀v,b v≤k)
local notation "Q" => (2^f*B:ℕ)
local notation "traffic" => fun v z i=>(flow v z i:ℝ)
local notation "X" => fun (v : V) (i : Bits k)=>weight v (address k i)
local notation "Y" => fun (c : Contacts near) (i : Bits k)=>flow (Sigma.fst c) (Subtype.val (Sigma.snd c)) (address k i)
local notation "M" => ∑c : Contacts near,∑i,(flow (Sigma.fst c) (Subtype.val (Sigma.snd c)) i:ℝ)
local notation "W" => mixingWeightNumerator (inputLevels (k:=k) b) (inputDepth b) (pairDepth near b) X Y f B K

omit [DecidableEq V] in
private theorem measured_bounds {ε : ℝ} (geom : BaseGeometry near Δ r f B K ε weight traffic b)
    (room : ∀v i,weight v i≤B) (hB : 0<B) (inc : ∀v i,∑z∈near v,flow v z i≤weight v i) :
    (∀v i,((X v i:ℕ):ℝ)/(Q:ℝ)≤1/(2:ℝ)^f) ∧
    (∀v,∑i,((X v i:ℕ):ℝ)/(Q:ℝ)≤(2:ℝ)^b v) ∧
    (∀c i,((Y c i:ℕ):ℝ)/(Q:ℝ)≤1/(2:ℝ)^f) ∧
    (∑c,∑i,((Y c i:ℕ):ℝ)/(Q:ℝ))≤M/((2:ℝ)^f*B) := by
  have raw (a : ℕ) (small : a≤B) : (a:ℝ)/(Q:ℝ)≤1/(2:ℝ)^f := by
    push_cast
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right (by exact_mod_cast small : (a:ℝ)≤B) (show (0:ℝ)≤2^f by positivity)]
  refine ⟨fun v i=>raw _ (room v _),?_,?_,?_⟩
  · intro v
    calc
      _ = ∑i,normalized weight (Q:ℝ) v i := (address k).sum_comp _
      _ ≤ _ := by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using geom.density v
  · intro c i
    have one := Finset.single_le_sum (f:=fun z=>flow c.1 z (address k i)) (fun _ _=>Nat.zero_le _) c.2.property
    exact raw _ ((one.trans (inc _ _)).trans (room _ _))
  · have sum (c : Contacts near) : (∑i : Bits k,(flow c.1 c.2.val (address k i):ℝ))=
        ∑i : Block k,(flow c.1 c.2.val i:ℝ) :=
      (address k).sum_comp (fun i : Block k=>(flow c.1 c.2.val i:ℝ))
    simp only [←Finset.sum_div,sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,le_refl]

set_option maxHeartbeats 800000 in
/-- A true loaded autocorrelation bank determines the frame's matrix and the
marked geometry together. No optimum is selected after reading the output. -/
theorem mixer_paid (sym : ∀v z,z∈near v ↔ v∈near z) (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ)
    (hB : 0<B) (hK : 0<K) (limits : ∀v i,weight v i≤B) (inc : ∀v i,∑z∈near v,flow v z i≤weight v i)
    (ε : ℝ) (ep : 0≤ε) (hh : 0<hops) (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (geom : BaseGeometry near Δ r f B K ε weight traffic b)
    (bank : ℕ→ℕ) (initial : Layout k) (m : Memory w) (space : Room w k base bank)
    (scaleBits countBits gainBits massBits : ℕ) (scaleBound : Q≤2^scaleBits)
    (members : (∑v,inputLevels (k:=k) b v)+Fintype.card (Contacts near)≤2^countBits)
    (gain : ∀v (s : Fin (inputLevels (k:=k) b v)),4*2^((s.val+7)/8)≤2^gainBits)
    (rate : K^2≤2^gainBits) (loadBits : ∀v,(∑i,X v i)≤2^massBits) (flowBits : ∀c,(∑i,Y c i)≤2^massBits)
    (fits : 3*k+(scaleBits+countBits+gainBits+2*massBits)+2≤w)
    (physical : ∀(l : Fin (k+1)) (z : Fin (2^k)),m (bank l.val+z.val)=(W l (DescentGLScoreRAM.vec z):Word w)) :
    let out := finalMemory k base bank m
    (program w k base bank).Exec m out (time k base bank k+DescentGLPermutationRAM.clock k) ∧
    ∃μ : Layout k,PaidResetLayout near Δ r f B K hops ε weight traffic b hk μ ∧
      (∀j : Fin k,out (pointer k base j.val)=((rowIndex k (rowFunctional μ j)).val:Word w)) ∧
      (∀z : Fin (2^k),out (outputBase k base+z.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm z))).val:Word w)) ∧ ∀a<base,out a=m a := by
  obtain ⟨lo,load,thin,total⟩ := measured_bounds near weight flow b geom limits hB inc
  obtain ⟨run,μ,upper,rows,table,frame⟩ := physical_mixing_layout (F:=f) (B:=B) (K:=K) (inputLevels b) (inputDepth b) (inputFits b hk)
    (pairDepth near b) (pairFits near b hk) X Y bank m space initial hB (fun v=>(2:ℝ)^b v) M
    (fun _ _=>by simp [inputDepth,pow_add]) (fun _=>by positivity)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using lo)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using load)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using thin)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using total)
    scaleBits countBits gainBits massBits scaleBound members gain rate loadBits flowBits fits physical
  refine ⟨run,μ,paid_of_measured_potential near sym branch degree hB hK weight limits traffic
    (fun v i=>by exact_mod_cast inc v i) ε ep hh small b hk geom μ ?_,rows,table,frame⟩
  simpa only [truePotential,resetTail,normalized,Function.comp_def,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using upper

/-- The complete mixer can materialize its score bank before the cut. It
returns the integral collision objective below its exact finite average.
That weaker native receipt already suffices for the same installed layout. -/
theorem paid_of_subaverage (sym : ∀v z,z∈near v ↔ v∈near z) (branch : 2≤Δ)
    (degree : ∀v,(near v).card≤Δ) (hB : 0<B) (hK : 0<K) (limits : ∀v i,weight v i≤B)
    (inc : ∀v i,∑z∈near v,flow v z i≤weight v i) (ε : ℝ) (ep : 0≤ε) (hh : 0<hops)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (geom : BaseGeometry near Δ r f B K ε weight traffic b) (μ : Layout k)
    (paid : allDepthCollisionCost (Weights W Q) μ≤
      (∑L : Layout k,allDepthCollisionCost (Weights W Q) L)/Fintype.card (Layout k)) :
    PaidResetLayout near Δ r f B K hops ε weight traffic b hk μ := by
  obtain ⟨lo,load,thin,total⟩ := measured_bounds near weight flow b geom limits hB inc
  let x := fun (v:V) i=>((X v i:ℕ):ℝ)/(Q:ℝ)
  let y := fun (c:Contacts near) i=>((Y c i:ℕ):ℝ)/(Q:ℝ)
  let levels := inputLevels (k:=k) b
  let j := inputDepth (k:=k) b
  let hj := inputFits b hk
  let cj := pairDepth near b
  let hcj := pairFits near b hk
  let weights := mixingCollisionWeights levels j hj cj hcj x y f B K
  let rest := mixingOffset levels j cj x y f B K
  let cost := mixingPotential levels j hj cj hcj x y f B K
  have weightEq : weights=Weights W Q := by
    funext l d
    exact mixingCollisionWeights_eq_integer levels j hj cj hcj X Y f B K l d
  have split : cost=fun T=>rest+allDepthCollisionCost (Weights W Q) T := by
    rw [←weightEq]
    exact funext (mixingPotential_eq levels j hj cj hcj x y f B K)
  let : Nonempty (Layout k) := ⟨μ⟩
  have shifted : average cost=rest+average (allDepthCollisionCost (Weights W Q)) := by
    rw [split]
    calc
      _ = average (fun _ : Layout k=>rest)+average (allDepthCollisionCost (Weights W Q)) := by
        simp only [average,Finset.sum_add_distrib,add_div]
      _ = _ := by rw [average_const]
  have localBound : cost μ≤average cost := by
    rw [shifted,congrFun split μ]
    exact add_le_add (le_refl rest) paid
  have avg := average_mixing_layout k f levels j hj cj hcj x (fun v=>(2:ℝ)^b v) y B K M
    (by exact_mod_cast hB) (fun _ _=>by simp [j,inputDepth,pow_add]) (fun _=>by positivity)
    (fun v i=>by dsimp [x];positivity) lo load (fun c i=>by dsimp [y];positivity) thin total
  apply paid_of_measured_potential near sym branch degree hB hK weight limits traffic
    (fun v i=>by exact_mod_cast inc v i) ε ep hh small b hk geom μ
  simpa only [truePotential,resetTail,cost,x,y,levels,j,hj,cj,hcj,normalized,Function.comp_def,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using localBound.trans avg

end
end Hierarchy.DescentColonies

end OAI
