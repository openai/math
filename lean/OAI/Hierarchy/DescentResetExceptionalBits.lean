import OAI.Hierarchy.DescentResetPlacementPrice
import OAI.Hierarchy.DescentChosenRouterNames

namespace OAI
/-! # Integer tests for the exceptional base keys of the chosen reset -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance DescentBaseProfile
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

def binLoad {I Q : Type*} [Fintype I] [DecidableEq Q] (table : I→ℕ) (group : I→Q) (q : Q) : ℕ :=
  ∑i,if q=group i then table i else 0

theorem capacity_integer {I : Type*} [Fintype I] {j : ℕ} (table : I→ℕ) (group : I→Block j)
    (q : Block j) {scale K : ℕ} (hs : 0<scale) (hK : 0<K) :
    mean (fun i=>(table i:ℝ)/scale) (Block j)+1/K <
      load group (fun i=>(table i:ℝ)/scale) q ↔
    K*(∑i,table i)+scale*2^j < K*2^j*binLoad table group q := by
  have whole : (∑i,(table i:ℝ)/scale)=((∑i,table i):ℕ)/ (scale:ℝ) := by
    rw [←Finset.sum_div,Nat.cast_sum]
  have part : load group (fun i=>(table i:ℝ)/scale) q=(binLoad table group q:ℝ)/scale := by
    simp only [load,binLoad,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  rw [mean,whole,part,show Fintype.card (Block j)=2^j from Fintype.card_fin _]
  have kp : (0:ℝ)<K := by exact_mod_cast hK
  have sp : (0:ℝ)<scale := by exact_mod_cast hs
  have jp : (0:ℝ)<(2:ℕ)^j := by positivity
  push_cast at *
  rw [←Nat.cast_lt (α:=ℝ)]
  push_cast
  constructor <;> intro ineq <;> field_simp [ne_of_gt kp,ne_of_gt sp] at * <;> nlinarith

/-- The split flag and the capacity-failure marks use the same rearranged
original labels and preserve coincident marks at both endpoints. -/
theorem resetKeys_iff (near : V→Finset V) (Δ f B K : ℕ) (hb : 0<B) (hkpos : 0<K)
    (weight : V→Block k→ℕ) (traffic : V→V→Block k→ℕ) (b : V→ℕ) (depth : ∀v,b v≤k)
    (L : Layout k) (v : V) (id : ℕ) :
    (v,id)∈resetKeys near Δ f B K weight (fun v w i=>(traffic v w i:ℝ)) b depth L ↔
    (∃x : Block k,Split (rearrangedLoad weight L) (fun v w=>w∈near v) (32*Nat.clog 2 (2*Δ))
      (2*(2^f*B)) v (b v) x ∧ group (b v) x=id) ∨
    ∃ e : Contacts near,∃q : Block (max (b e.1) (b e.2.val)),
      K*(∑i,traffic e.1 e.2.val i)+(2^f*B)*2^(max (b e.1) (b e.2.val)) <
        K*2^(max (b e.1) (b e.2.val))*binLoad (traffic e.1 e.2.val)
          (dyadicLayout (max_le (depth e.1) (depth e.2.val)) L) q ∧
      ((reservationEndpoints b (fun e:Contacts near=>e.1) (fun e=>e.2.val) e q).1=(v,id) ∨
       (reservationEndpoints b (fun e:Contacts near=>e.1) (fun e=>e.2.val) e q).2=(v,id)) := by
  simp only [resetKeys,Finset.mem_union,forced,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and,capacityEnds,Finset.mem_insert,Finset.mem_singleton]
  apply or_congr
  · constructor
    · rintro ⟨u,x,h,eqn⟩
      obtain ⟨rfl,idEq⟩:=Prod.mk.inj eqn
      exact ⟨x,h,idEq⟩
    · rintro ⟨x,h,eqn⟩
      exact ⟨v,x,h,Prod.ext rfl eqn⟩
  · apply exists_congr
    intro e
    apply exists_congr
    intro q
    apply and_congr
    · exact capacity_integer _ _ _ (Nat.mul_pos (Nat.two_pow_pos _) hb) hkpos
    · simp only [eq_comm]

end
end Hierarchy.DescentColonies

end OAI
