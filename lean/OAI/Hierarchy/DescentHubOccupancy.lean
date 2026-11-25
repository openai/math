import OAI.Hierarchy.DescentPackedVenueOrdinals
import OAI.Hierarchy.DescentNextCoordinates
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # Every allocated external hub row has a real occurrence in each new block -/

namespace Hierarchy.DescentHostDirectory
open DescentColonies DescentSixParty.StarKeys Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {J V G : Type} [Fintype J] [Fintype V] [Fintype G]
variable [DecidableEq J] [DecidableEq V] [DecidableEq G]
variable {k g slots step : ℕ}

/-- Only the actual merged depth and slot zero at an exterior position
designate a hub. Other addresses in the common finite directory are ordinary. -/
def publishedHub (hub : V→Bool) (k g : ℕ) (u : Key V) : Bool :=
  hub u.1 && decide (u.2.1.1=k-g ∧ u.2.2=0)

theorem hub_block (gk : g≤k) {id : ℕ} (h : id<2^(k-g)) :
    ∃b : Block k,group (k-g) b=id := by
  have cap : 2^(k-g)*2^g=(2:ℕ)^k := by rw [←pow_add,Nat.sub_add_cancel gk]
  let x : Block k := ⟨id*2^g,cap ▸ Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)⟩
  refine ⟨x,?_⟩
  simp [group,width,x,Nat.sub_sub_self gk]

variable {d : ℕ} {P S : Type} [Fintype S] {bits : P→ℕ} (N : Network d P bits)
variable (pos : N.Site→J×V) (ix : N.Site→Block k) (full : N.Site→ℕ)
variable (out : N.Site→S) (addr : S↪Key (J×V))
variable (digits : J≃G×Block step) (ok : ∀u,(splitKey (addr u)).2∈keys k slots)

omit [DecidableEq J] [DecidableEq V] in
theorem split_mem (x : Key (J×V)) (valid : x∈keys k slots) : (splitKey x).2∈keys k slots :=
  Finset.mem_product.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp valid).2⟩

omit [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V] in
theorem grouped_flag {v : Key (J×V)} (flag : V→Bool)
    (physical : flag v.1.2=true→v.2.1.1=k-g ∧ v.2.2=0) :
    publishedHub flag k g (splitKey v).2=flag v.1.2 := by
  change (flag v.1.2 && decide (v.2.1.1=k-g ∧ v.2.2=0))=flag v.1.2
  cases h : flag v.1.2 with
  | false => rfl
  | true => simp [(physical h).1,(physical h).2]

omit [Fintype J] [Fintype G] [DecidableEq G] [Fintype S] in
/-- The next common host is allocated before the choice of branch. A
prescribed hub address in it is nevertheless inhabited on every new digit,
directly from the old full block mass. -/
theorem realized_hub (hub : V→Bool) (B : ℕ) (positive : 0<B) (gk : g≤k)
    (filled : ∀v,hub v.2=true→∀i,blockMass N pos ix full v i=B)
    (forward : ∀u,hub (pos u).2=true→
      addr (out u)=(pos u,(k-g,group (k-g) (ix u)),0))
    (v : G×Host V k slots) (i : Block step) (trueHub : publishedHub hub k g v.2.val=true) :
    ∃u : S,nextPos addr digits ok u=v ∧ nextBlock addr digits u=i := by
  rcases v with ⟨c,⟨⟨v,⟨d,j⟩,slot⟩,valid⟩⟩
  have active : hub v=true ∧ d=k-g ∧ slot=0 := by simpa [publishedHub] using trueHub
  obtain ⟨yes,rfl,rfl⟩ := active
  have id := (codes_valid (Finset.mem_product.mp (Finset.mem_product.mp valid).2).1).2
  obtain ⟨b,hb⟩ := hub_block gk id
  let high := digits.symm (c,i)
  have existsSite : ∃u,pos u=(high,v) ∧ ix u=b := by
    by_contra! missing
    have zero : blockMass N pos ix full (high,v) b=0 := by
      apply Finset.sum_eq_zero
      intro u _
      exact ite_eq_right (fun h=>missing u h.1 h.2)
    rw [filled _ yes b] at zero
    omega
  obtain ⟨u,place,index⟩ := existsSite
  have hu : hub (pos u).2=true := by rw [place];exact yes
  have done := forward u hu
  rw [place,index,hb] at done
  refine ⟨out u,?_,?_⟩
  · apply Prod.ext
    · change (digits (addr (out u)).1.1).1=c
      rw [done]
      exact congrArg Prod.fst (digits.apply_symm_apply (c,i))
    · apply Subtype.ext
      change ((addr (out u)).1.2,(addr (out u)).2)=(v,(k-g,j),0)
      rw [done]
  · change (digits (addr (out u)).1.1).2=i
    rw [done]
    exact congrArg Prod.snd (digits.apply_symm_apply (c,i))

omit [Fintype J] [Fintype G] in
/-- A positive hub is saturated in the common *block array*, including
when other gate positions in that same preallocated host are absent. -/
theorem complete_hub_mass (hub : V→Bool) (B : ℕ) (positive : 0<B) (gk : g≤k)
    (filled : ∀v,hub v.2=true→∀i,blockMass N pos ix full v i=B)
    (forward : ∀u,hub (pos u).2=true→addr (out u)=(pos u,(k-g,group (k-g) (ix u)),0))
    (charge : S→ℕ) (saturated : ∀u,publishedHub hub k g (splitKey (addr u)).2=true→charge u=2^g*B)
    (v : G×Host V k slots) (i : Block step) (isHub : publishedHub hub k g v.2.val=true) :
    (∑u,if nextPos addr digits ok u=v ∧ nextBlock addr digits u=i then charge u else 0)=2^g*B := by
  obtain ⟨u,p,b⟩ := realized_hub N pos ix full out addr digits ok hub B positive gk filled forward v i isHub
  rw [←p,←b,next_full_at]
  apply saturated
  simpa only [←p,nextPos] using isHub

end
end Hierarchy.DescentHostDirectory

end OAI
