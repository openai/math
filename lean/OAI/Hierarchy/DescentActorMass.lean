import OAI.Hierarchy.DescentTrunkWorld
import OAI.Hierarchy.DescentResetQuantum
import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentSubstitutionDegree

namespace OAI
/-! # Actual endpoint loads at the three kinds of sites after a physical reset -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentRouterBank DescentNamedContact DescentResetAttachments Computability.BorderVNP.Crossing
open DescentNetworkSubstitution
open scoped BigOperators Classical
noncomputable section

def bin {I J : Type*} [Fintype I] (f : I→J) (w : I→ℕ) (j : J) :=
  ∑i,if f i=j then w i else 0

theorem width_bin {I J : Type} [Fintype I] (f : I→J) (w : I→ℕ) (j : J) :
    DescentNamedContact.width f w j=bin f w j := by
  unfold DescentNamedContact.width bin
  rw [←Finset.sum_subtype (p:=fun i : I=>f i=j) (Finset.univ.filter (fun i : I=>f i=j))
    (by simp) w,Finset.sum_filter]

theorem bin_comp {I J K : Type*} [Fintype I] [Fintype J]
    (f : I→J) (g : J→K) (w : I→ℕ) (k : K) :
    bin g (bin f w) k=bin (g ∘ f) w k := by
  unfold bin
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro j _ ne
    simp [Ne.symm ne]
  · simp

theorem bin_add {I J : Type*} [Fintype I] (f : I→J) (a b : I→ℕ) (j : J) :
    bin f (a+b) j=bin f a j+bin f b j := by
  simp [bin,←Finset.sum_add_distrib,←ite_add_zero]

theorem bin_mul {I J : Type*} [Fintype I] (f : I→J) (a : I→ℕ) (j : J) (c : ℕ) :
    bin f (fun i=>c*a i) j=c*bin f a j := by simp [bin,Finset.mul_sum,mul_ite]

theorem bin_factor {I J : Type*} [Fintype I] (f : I→J) (a : I→ℕ) (c : J→ℕ) (j : J) :
    bin f (fun i=>a i*c (f i)) j=bin f a j*c j := by
  simp only [bin,Finset.sum_mul,ite_mul,zero_mul]
  apply Finset.sum_congr rfl
  intro i _
  split <;> rename_i eq
  · rw [eq]
  · rfl

variable {F H P Q Aty Bty : Type} [Field F] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (grp : Bool→A.graph.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth grp A.graph.width)) (S : R.Tables F) (hub : H→Bool)
local notation "M" => world A home grp R S hub
local notation "tag" => hubAt A home grp R hub
variable (record : (world A home grp R S hub).graph.Site→List Bty) (wire β hist : ℕ)

omit [Field F] in
theorem endpoint_units (tag₀ : A.graph.Site→Bool) (x : A.graph.Site) (old : A.graph.Site→List Aty) :
    A.siteUnits tag₀ old wire β hist x=
      (bin A.graph.src A.graph.width x+bin A.graph.dst A.graph.width x)*wire*
        (if tag₀ x then β else 1)+hist*(old x).length := by
  have side (p : A.graph.Edge → A.graph.Site) :
      (∑e, if x=p e then wire*A.graph.width e*(if tag₀ (p e) then β else 1) else 0) =
      bin p A.graph.width x * wire * (if tag₀ x then β else 1) := by
    simp only [bin, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : p e=x
    · simp only [h]
      exact congrArg (fun z : ℕ => z*(if tag₀ x then β else 1)) (Nat.mul_comm wire _)
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), Nat.zero_mul]
  rw [MarkedWorld.siteUnits,side A.graph.src,side A.graph.dst]
  ring

omit [Fintype Q] in
/-- The two oriented old-edge rows, the trunks and the internal router rows
are the four disjoint parts of the reset network's edge table. -/
private theorem reset_bin (loc : (world A home grp R S hub).graph.Edge →
      (world A home grp R S hub).graph.Site) (x : (world A home grp R S hub).graph.Site) :
    bin loc (M).graph.width x =
      ((∑e : A.graph.Edge, if loc (.inl (true,e))=x then A.graph.width e else 0) +
       (∑e : A.graph.Edge, if loc (.inl (false,e))=x then A.graph.width e else 0)) +
      ((∑z : H, if loc (.inr (.inl z))=x then trunkWidth A.graph home z else 0) +
       (∑e : R.Edge, if loc (.inr (.inr e))=x then R.width e else 0)) := by
  let weightAt (e : (network A.graph home grp R).Edge) :=
    if loc e=x then (M).graph.width e else 0
  have physical : bin loc (M).graph.width x =
      ∑e : (network A.graph home grp R).Edge, weightAt e := rfl
  rw [physical, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool]; rfl

omit [Fintype Q] in
private theorem actor_bins (s : Bool) (t : H) :
    bin (M).graph.src (M).graph.width (.inl (s,t)) + bin (M).graph.dst (M).graph.width (.inl (s,t)) =
      bin (home ∘ DescentResetAttachments.ends A.graph s) A.graph.width t + trunkWidth A.graph home t := by
  classical
  refine (congrArg₂ Nat.add
    (reset_bin A home grp R S hub (M).graph.src (.inl (s,t)))
    (reset_bin A home grp R S hub (M).graph.dst (.inl (s,t)))).trans ?_
  cases s <;> simp [bin,world,DescentResetTrunks.network,DescentResetAttachments.ends,
    Function.comp_apply]
  · apply Finset.sum_congr (by ext e; simp)
    intro e _
    by_cases hit : home (A.graph.src e)=t <;> simp [hit]
  · apply Finset.sum_congr (by ext e; simp)
    intro e _
    by_cases hit : home (A.graph.dst e)=t <;> simp [hit]

omit [Fintype Q] in
theorem terminal_units (t : H) :
    (M).siteUnits tag record wire β hist (.inl (false,t))=
      (bin (home ∘ A.graph.src) A.graph.width t+bin (home ∘ A.graph.dst) A.graph.width t)*
      wire*(if hub t then β else 1)+hist*(record (.inl (false,t))).length := by
  have dst : trunkWidth A.graph home t = bin (home ∘ A.graph.dst) A.graph.width t :=
    width_bin (moved A.graph home) A.graph.width t
  refine (endpoint_units (Aty:=Bty) (M) wire β hist tag (.inl (false,t)) record).trans ?_
  rw [actor_bins A home grp R S hub false t,dst]
  by_cases marked : hub t=true <;> simp [DescentResetAttachments.ends,hubAt,marked]

omit [Fintype Q] in
theorem relay_units (t : H) :
    (M).siteUnits tag record wire β hist (.inl (true,t))=
      2*wire*bin (home ∘ A.graph.dst) A.graph.width t+hist*(record (.inl (true,t))).length := by
  have dst : trunkWidth A.graph home t = bin (home ∘ A.graph.dst) A.graph.width t :=
    width_bin (moved A.graph home) A.graph.width t
  refine (endpoint_units (Aty:=Bty) (M) wire β hist tag (.inl (true,t)) record).trans ?_
  rw [actor_bins A home grp R S hub true t,dst]
  change ((bin (home ∘ A.graph.dst) A.graph.width t + bin (home ∘ A.graph.dst) A.graph.width t)*wire*1) +
    hist*(record (.inl (true,t))).length = _
  ring

/-- A router actor is charged for the two ends of internal cables and for
each incident public terminal exactly as in its actual open gadget. -/
theorem bank_units (t : R.Site) :
    (M).siteUnits tag record wire β hist (.inr t)=wire*portLoad R t+hist*(record (.inr t)).length := by
  have contacts (s : Bool) :
      (∑q,if R.attach (s,q)=t then publicWidth grp A.graph.width (s,q) else 0)=
      ∑e,if R.attach (s,grp s e)=t then A.graph.width e else 0 := by
    change bin (fun q=>R.attach (s,q)) (DescentNamedContact.width (grp s) A.graph.width) t=_
    rw [show DescentNamedContact.width (grp s) A.graph.width=bin (grp s) A.graph.width from
      funext (width_bin (grp s) A.graph.width)]
    exact bin_comp (grp s) (fun q=>R.attach (s,q)) A.graph.width t
  have pins : (∑p : Bool × Q, if R.attach p=t then publicWidth grp A.graph.width p else 0) =
      (∑e, if R.attach (true,grp true e)=t then A.graph.width e else 0) +
      (∑e, if R.attach (false,grp false e)=t then A.graph.width e else 0) := by
    rw [Fintype.sum_prod_type,Fintype.sum_bool,contacts true,contacts false]
  have mass : bin (M).graph.src (M).graph.width (.inr t) +
      bin (M).graph.dst (M).graph.width (.inr t) = portLoad R t := by
    refine (congrArg₂ Nat.add
      (reset_bin A home grp R S hub (M).graph.src (.inr t))
      (reset_bin A home grp R S hub (M).graph.dst (.inr t))).trans ?_
    rw [portLoad_eq R t,pins]
    simp [world,DescentResetTrunks.network]; ac_rfl
  refine (endpoint_units (Aty:=Bty) (M) wire β hist tag (.inr t) record).trans ?_
  rw [mass]
  change portLoad R t*wire*1+hist*(record (.inr t)).length = _
  rw [Nat.mul_one, Nat.mul_comm (portLoad R t) wire]

omit [Fintype H] [Field F] in
theorem whole_fiber (old : A.graph.Site→List Aty) (t : H) :
    bin home (A.siteUnits (hub ∘ home) old wire β hist) t=
      (bin (home ∘ A.graph.src) A.graph.width t+bin (home ∘ A.graph.dst) A.graph.width t)*wire*
        (if hub t then β else 1)+hist*bin home (fun u=>(old u).length) t := by
  have entries : A.siteUnits (hub ∘ home) old wire β hist =
      ((fun u=>(bin A.graph.src A.graph.width u+bin A.graph.dst A.graph.width u)*wire*
        (if hub (home u) then β else 1)) + fun u=>hist*(old u).length) :=
    funext fun x=>endpoint_units A wire β hist (hub ∘ home) x old
  rw [entries,bin_add,bin_mul,bin_factor home _ (fun z=>if hub z then β else 1)]
  simp_rw [mul_comm _ wire]
  rw [bin_mul,show (fun u=>bin A.graph.src A.graph.width u+bin A.graph.dst A.graph.width u)=
    bin A.graph.src A.graph.width+bin A.graph.dst A.graph.width from rfl,bin_add,bin_comp,bin_comp]

omit [Fintype Q] in
theorem grouped_units (old : A.graph.Site→List Aty) (t : H)
    (words : (record (.inl (false,t))).length=bin home (fun u=>(old u).length) t) :
    (M).siteUnits tag record wire β hist (.inl (false,t))=
      bin home (A.siteUnits (hub ∘ home) old wire β hist) t := by
  rw [terminal_units,words,whole_fiber A home hub wire β hist]

end
end Hierarchy.DescentResetTrunks

end OAI
