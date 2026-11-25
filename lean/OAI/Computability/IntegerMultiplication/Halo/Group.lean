import OAI.Computability.IntegerMultiplication.Halo.Color

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Finset Cone Grid Axon
noncomputable section
variable {n k f:ℕ}
section slit
variable {X S α:Type}
-- abstract pulls along oriented group
def orbit (e : Tri n ≃ X × S) (o:(X→α)→X→α) : (Tri n→α)→Tri n→α :=
  fun g i=>
    let u:=e i
    o (fun v=>g (e.symm (v,u.2))) u.1
@[simp] theorem cup (e : Tri n ≃ X × S) (o:(X→α)→X→α) (x:Tri n→α) (a:X) (s:S) :
    orbit e o x (e.symm (a,s)) = o (fun b=>x (e.symm (b,s))) a := by simp only [orbit,Equiv.apply_symm_apply]
variable (e : Tri n≃xy k f×S) (q:Fin f → Bits.Word) (b:ℕ→ Cone.G n)
theorem orbit_r (odd:∀ i,Odd (Bits.value (q i)))
    (a:∀ i:Fin (2^k), ‖Cone.look n (b i)-Axon.R k (i.val:ℕ)‖ ≤err n)
    (t:(f+2)*k≤P n):
    Flow 750 1 2 (orbit e (color q b)) (orbit e (trueC q)) where
  norm_ _B u v x w i := (cert q b odd a t (fun c=>x (e.symm (c,(e i).2)))
    u v (fun _j=>w _)).1 ((e i).1)
  delta _B u v x w i := (cert q b odd a t (fun c=>x (e.symm (c,(e i).2))) u v
    (fun _j=>w _)).2 ((e i).1)
  normal _B p x y h i :=
    colorNorm q p (fun c=>x (e.symm (c,(e i).2))) (fun c=>y (e.symm (c,(e i).2))) (fun _c=>h _) t ((e i).1)

end slit
variable (h:Season n)
abbrev sightA : Tri n ≃ xy (ell n) (Focn n) × (sucV n × dayV n) := prism h
abbrev unscrew (y: Spot (2^k)) : xy k 1:=fun _=>y
def lonely : Spot (2^k)≃xy k 1 where
  toFun:= unscrew
  invFun x:=x 0
  left_inv _:=rfl
  right_inv x := by
    funext i
    change x 0=x i
    exact congrArg x (Subsingleton.elim _ _)
def rayB : Jade n≃ xy (reach n) 1 × (primeV n × dayV n) where
  toFun x := (lonely x.2.1,x.1,x.2.2)
  invFun y:= (y.2.1,lonely.symm y.1,y.2.2)
  left_inv x:=by
    rcases x with ⟨a,b,c⟩
    change Spot (2^reach n) at b
    simp [Equiv.symm_apply_apply]
  right_inv y:=by simp
def rayC : Jade n≃ xy (ell n) 1 × (primeV n × sucV n) where
  toFun x:=(lonely x.2.2,x.1,x.2.1)
  invFun y:= (y.2.1,y.2.2,lonely.symm y.1)
  left_inv x:=by
    rcases x with ⟨a,b,c⟩
    change Spot (2^ell n) at c
    simp [Equiv.symm_apply_apply]
  right_inv y:=by simp
abbrev sightB := (prism h).trans (rayB (n:=n))
abbrev sightC := (prism h).trans (rayC (n:=n))

-- true shore q arrays; proof costs
abbrev wordN (k : ℕ)(i:Direction n) := Bits.short k (modulus n i)
abbrev wordA (n): Scouts n→Bits.Word := fun i=>wordN (ell n) (rook i)
abbrev wordB (_: Fin 1) := wordN (reach n) (near h)
abbrev wordC (_: Fin 1) := wordN (ell n) (rear h)
include h
theorem pricedN {k}(i:Direction n) (v:criterion n i=2^k):
    Bits.value (wordN k i)=modulus n i := by
  rw [Bits.value_short]
  apply Nat.mod_eq_of_lt
  rw [← v]
  exact (h.margin i i.isLt).strict (Nat.pos_of_ne_zero (NeZero.ne _)) (lanes_pos _)
theorem pricedA (i: Scouts n):
    Bits.value (wordA n i)=modulus n (rook i):=
  pricedN h (rook i) (rook_f _)
theorem paidA :(Focn n+2)*ell n ≤P n := by
  have p:Focn n+2=lanes n := by have v:=h.dim; unfold Focn scouts; omega
  rw [p]; exact wall_small n
theorem paidB :(1+2)*reach n ≤ P n := by
  let k:=reach n
  have v:=h.shortWidth
  have Q: reach n ≤ ell n:=by omega
  exact (Nat.mul_le_mul (h.dim) Q).trans (wall_small n)
theorem paidC :(1+2)*ell n ≤ P n :=
  le_trans (Nat.mul_le_mul_right _ (h.dim)) (wall_small n)

-- bank adaptation same phase
abbrev shortBank (b:ℕ→ Cone.G n)(i:ℕ) := b (2^slack n*i)
theorem mint (b:ℕ→ Cone.G n)
    (a:∀ i:Fin (wall n), ‖Cone.look n (b i)-Axon.R (ell n) (i.val:ℕ)‖ ≤err n)
    (i:Fin (room n)):
    ‖Cone.look n (shortBank b i)-Axon.R (reach n) (i.val:ℕ)‖ ≤ err n := by
  have e:slack n+reach n=ell n:=by have v:=h.shortWidth; omega
  let S:= 2^slack n
  have v : S*i.val < wall n := by
    change _ < 2^ell n
    rw [← e,pow_add]
    exact Nat.mul_lt_mul_of_pos_left i.isLt (by unfold S; positivity)
  have w:=a ⟨_,v⟩
  suffices Axon.R (ell n) ((S*i.val:ℕ):ℤ) = Axon.R (reach n) (i.val:ℤ) by rw [this] at w; exact w
  unfold Axon.R phase S
  rw [← e,pow_add]; congr 1
  push_cast
  field_simp

abbrev Ho (b:ℕ→ Cone.G n) :=
  orbit (sightA h) (color (wordA n) b)
abbrev Hs (b:ℕ→ Cone.G n) :=
  orbit (sightB h) (color (wordB h) (shortBank b))
abbrev Hl (b:ℕ→ Cone.G n) :=
  orbit (sightC h) (color (wordC h) b)
abbrev Fo : Land n→Land n:=orbit (sightA h) (trueC (wordA n))
abbrev Fs : Land n→Land n:=orbit (sightB h) (trueC (wordB h))
abbrev Fl : Land n→Land n:=orbit (sightC h) (trueC (wordC h))

abbrev umi (b:ℕ→ Cone.G n) := Hl h b ∘ Hs h b ∘ Ho h b
abbrev glen := Fl h ∘ Fs h ∘ Fo h
theorem career (b:ℕ→ Cone.G n) (a:∀ i:Fin (wall n), ‖Cone.look n (b i)-Axon.R (ell n) (i.val:ℕ)‖ ≤err n) :
    Flow 700 3 13 (umi h b) (glen h) := by
  have p : ∀ i:Direction n, Odd (modulus n i) := fun i=>h.odd _ i.isLt
  have A : Flow 750 1 2 (Ho h b) (Fo h) := orbit_r _ _ _
    (fun i=>pricedA h i ▸ p _) a (paidA h)
  have B : Flow 750 1 2 (Hs h b) (Fs h) := orbit_r (sightB h) _ _ (fun i=> (pricedN h _ (near_s h)) ▸ p _)
    (mint h b a) (paidB h)
  have C : Flow 750 1 2 (Hl h b) (Fl h) := orbit_r _ _ _ (fun i=> (pricedN h _ (rear_f h)) ▸ p _)
    a (paidC h)
  -- A→B→C. A→B: l2+2+1+1+1=7; then C =>7+2+2+1+1=13
  have Q := ((A.chain B 730 (by decide) (by decide)).chain C 700 (by decide) (by decide))
  exact Q
end
end Halo

end IntegerMultiplication
end Computability
end OAI
