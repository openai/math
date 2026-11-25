import OAI.Hierarchy.TaggedWideElectrical
import OAI.Hierarchy.TaggedWideBankCut
import OAI.Hierarchy.TaggedShorterCost
import OAI.Hierarchy.TaggedWidePoolPrice

namespace OAI
/-! # The finite wide host with the actual compactors and control cut words -/

noncomputable section
namespace Hierarchy.Tagged
open ThreeFlat Routing Spill Catalyst CatalystSubstitution
open TaggedShorterCompaction TaggedShorterNetwork TaggedPrune
open scoped Classical BigOperators

/-- A physical socket configuration. All fields are chosen before entering
the sum over selector, payload and native memory bits. -/
structure CutFormat (F : Type*) (V : Type) [Field F] where
  candidates : ℕ
  slots : ℕ
  modules : ℕ
  height : ℕ
  width : ℕ
  near : Compactor F slots (2^height) (height+width)
  far : Compactor F candidates modules (Width (2^height) (height+width))
  readPin : Input candidates slots (height+width) → V

namespace CutFormat
variable {F : Type*} {V : Type} [Field F] [Fintype V]

def bank (b : CutFormat F V) (cap : ℕ) : ShorterBank := ⟨b.height,b.width,b.modules*2,cap⟩

def cost (b : CutFormat F V) :=
  4*(b.far.network.cells+2*b.candidates*b.near.network.cells+
    b.modules*(lane F b.height b.height b.width).cells)+1

def closed (b : CutFormat F V) (v : V → Bool) :=
  TaggedShorterBank.close (TaggedShorterBank.cut b.near b.far (lane F b.height b.height b.width))
    (oracle F b.height b.width) (v ∘ b.readPin)

private theorem closed_eq_sum (b : CutFormat F V) (v : V → Bool) :
    b.closed v = ∑ z, TypedWiring.value (WideStack.sharedCut b.near b.far b.readPin)
      (Sum.elim v z) * CorrectionFrame.dataProduct (b.modules*2) (coeff F b.height b.width) z :=
  (WideStack.sharedCut_contract b.near b.far b.readPin v).symm

/-- The same compactors realizing the required bit predicate have the
linear-volume price used by the global socket compiler. The constant is
uniform over all types and all parent heights. -/
theorem purchased (F : Type*) [Field F] :
    ∃ cutoff c : ℕ, ∀ {V : Type} [Fintype V] (S D M h w L : ℕ)
      (read : Input S D (h+w) → V), 2^h≤D → cutoff≤2*2^h → 0<M → M≤S → cutoff≤2*M →
      Nat.log 2 S≤L → Nat.log 2 D≤L →
      ∃ (near : Compactor F D (2^h) (h+w)) (far : Compactor F S M (Width (2^h) (h+w))),
        (CutFormat.mk S D M h w near far read).cost ≤
          4*TaggedShorterCost.cost S D M (2^h) c (L+h+h+w+5)+1 := by
  obtain ⟨cutoff,c,make⟩ := TaggedShorterCost.exists_boards_raw F
  refine ⟨cutoff,c,fun {V} _ S D M h w L read scale big positive count enough sBound dBound => ?_⟩
  obtain ⟨near,far,bill⟩ := make S D M h h w L scale big positive count enough sBound dBound
  exact ⟨near,far,Nat.add_le_add_right (Nat.mul_le_mul_left 4 bill) 1⟩

omit [Fintype V] in
/-- Turn the two physical volume estimates (including idle modules) into
the ordinary cell/hidden-variable bill. L is an upper bound for both index
logarithms. The bit width T may include a polylogarithmic factor. -/
theorem cost_of_volumes (b : CutFormat F V) (c L : ℕ) {N T P Q : ℝ}
    (hN : 0≤N) (hP : 0≤P) (hQ : 0≤Q)
    (purchased : b.cost ≤ 4*TaggedShorterCost.cost b.candidates b.slots b.modules
      (2^b.height) c (L+b.height+b.height+b.width+5)+1)
    (candidates : (b.candidates:ℝ)*b.slots ≤ P*N)
    (installed : (b.modules:ℝ)*(2:ℝ)^b.height ≤ Q*N)
    (width : ((L+b.height+b.height+b.width+5:ℕ):ℝ)≤T) :
    (b.cost:ℝ) ≤ (4*(5*c*P+177000*Q))*N*T+1 := by
  let u := (L+b.height+b.height+b.width+5:ℕ)
  have lead : 5*(c:ℝ)*((b.candidates:ℝ)*b.slots)+177000*((b.modules:ℝ)*(2:ℝ)^b.height) ≤
      (5*c*P+177000*Q)*N := by
    calc
      _ ≤ 5*(c:ℝ)*(P*N)+177000*(Q*N) := by gcongr
      _ = _ := by ring
  have estimate : (b.cost:ℝ) ≤ 4*((5*(c:ℝ)*((b.candidates:ℝ)*b.slots)+
      177000*((b.modules:ℝ)*(2:ℝ)^b.height))*(u:ℝ))+1 := by
    change b.cost ≤ 4*((5*c*(b.candidates*b.slots)+177000*(b.modules*2^b.height))*u)+1 at purchased
    exact_mod_cast purchased
  refine estimate.trans ?_
  have product := mul_le_mul lead width (Nat.cast_nonneg u) (by positivity)
  linarith only [mul_le_mul_of_nonneg_left product (by norm_num : (0:ℝ)≤4)]

/-- No approximant occurs in the physical charge or the semantics of the
ideal installation. There is one occurrence per positive dyadic type. -/
theorem parts {n c k : ℕ} (b : Fin n → CutFormat F V) (cap : Fin n → ℕ) (t : Fin c → ℕ)
    (localPart : BitNetwork F (Fintype.card V)) (read : ∀ j,Fin (pins (t j) (t j)) → V)
    (Y : ∀ i,((b i).bank (cap i)).Output F k) (Z : ∀ j,Approximation F k (pins (t j) (t j))) :
    let B := fun i => (b i).bank (cap i)
    let os := bankCalls B Y (controlCalls t Z)
    ∃ pieces : WideHost.Parts F V os, (∀ v, WideHost.closed localPart os pieces v =
      (∏ i,(b i).closed v) * (∏ j, coeff F (t j) (t j) (v ∘ read j)) *
        TypedWiring.value localPart v) ∧
      WideHost.partsCost os pieces ≤ (∑ i,(b i).cost) + (∑ j,28*pins (t j) (t j)) := by
  intro B os
  obtain ⟨pieces,ev,work⟩ := parts_of_control_words B t localPart
    (fun i => WideStack.sharedCut (b i).near (b i).far (b i).readPin) read Y Z
  refine ⟨pieces,?_,?_⟩
  · intro v
    refine (ev v).trans ?_
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    apply Finset.prod_congr rfl
    intro i _
    rw [closed_eq_sum]
    apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro z _
    rfl
  · rw [work]
    apply Nat.add_le_add_right
    exact Finset.sum_le_sum fun i _ => WideStack.sharedCut_cost (b i).near (b i).far (b i).readPin

/-- Connect the purchased compactors to the nonuniform cofinal compiler.
The routed local contraction may inspect all selected source and destination
data jointly. All sites and cuts are fixed even before the user supplies
any shorter approximations to the induction. -/
theorem static_board {k h w M n c : ℕ} (routing : NativeRouting F k h w M)
    (b : Fin n → CutFormat F (OpenPins h w routing.catalyst ⊕ (Fin routing.selectors ⊕ routing.Shared)))
    (cap : Fin n → ℕ) (t : Fin c → ℕ)
    (localPart : BitNetwork F (Fintype.card (OpenPins h w routing.catalyst ⊕ (Fin routing.selectors ⊕ routing.Shared))))
    (read : ∀ j, Fin (pins (t j) (t j)) → OpenPins h w routing.catalyst ⊕ (Fin routing.selectors ⊕ routing.Shared))
    (eval : ∀ x s, (∑ y : routing.Shared → Bool, let v := Sum.elim x (Sum.elim s y)
      (∏ i,(b i).closed v)*(∏ j,coeff F (t j) (t j) (v ∘ read j))*TypedWiring.value localPart v) =
        selected (fun a => (routing.links a).Keep (2^h)) routing.encoding routing.route x s) :
    ∃ board : StaticBoard F k h w M (fun i=>(b i).bank (cap i)) t,
      board.selectors=routing.selectors ∧ board.cost ≤
        localPart.cells+localPart.internal+((∑ i,(b i).cost)+∑ j,28*pins (t j) (t j))+
        (routing.selectors+Fintype.card routing.Shared)+(Fintype.card (OpenPins h w routing.catalyst)+
        ((∑ i,((b i).modules*2)*pins (b i).height (b i).width)+∑ j,pins (t j) (t j))) := by
  let board : StaticBoard F k h w M (fun i=>(b i).bank (cap i)) t :=
    { toNativeRouting := routing, localPart := localPart, read := read,
      banks := fun i => WideStack.sharedCut (b i).near (b i).far (b i).readPin,
      realizes := fun x s => by
        refine (Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) ?_).trans (eval x s)
        intro y _
        dsimp only
        refine congrArg₂ (· * ·) ?_ rfl
        refine congrArg₂ (· * ·) ?_ rfl
        apply Finset.prod_congr rfl
        intro i _
        rw [closed_eq_sum]
        apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
        intro z _
        rfl }
  refine ⟨board,rfl,?_⟩
  have cost : (∑ i, ((WideStack.sharedCut (b i).near (b i).far (b i).readPin).cells+
      (WideStack.sharedCut (b i).near (b i).far (b i).readPin).internal)) ≤ ∑ i,(b i).cost :=
    Finset.sum_le_sum fun i _ => WideStack.sharedCut_cost (b i).near (b i).far (b i).readPin
  dsimp only [board,StaticBoard.cost,bank]
  omega

end CutFormat
end Hierarchy.Tagged

end
end OAI
