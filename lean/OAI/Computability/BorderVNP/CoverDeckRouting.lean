import OAI.Computability.BorderVNP.CoverDeckRoutingWords

/-!
# Routing by tile addresses in the quaternion congruence covers

The symmetric set of generators consists of fixed lifts at depths one, two
and three, together with their inverses. To reach a given tile we correct its
residue one layer at a time. At all depths from two on, three quadratic-length
words, one per imaginary coordinate, suffice. This proves the cubic diameter
bound of Lemma 5.1 in the actual deck group.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- A fixed lift of a first-layer residue in the image of the leading map. -/
noncomputable def liftFirst (r : (leading 0).range) : gamma 1 :=
  ((leading 0).rangeRestrict_surjective r).choose

/-- A fixed lift of a residue at depth two or three. -/
noncomputable def liftBase (d : Fin 2) (r : Layer) : gamma (d.val+2) :=
  (leading_surj d.val (Multiplicative.ofAdd r)).choose

private noncomputable def seeds : Finset Orderˣ := by
  classical
  exact (Finset.univ.image (fun r => (liftFirst r).val)) ∪
    Finset.univ.image (fun p : Fin 2 × Layer => (liftBase p.1 p.2).val)

/-- A symmetric finite subset of the level-one quaternion group, independent
of the depth at which it will be used. -/
noncomputable def routingGenerators : Finset Orderˣ := by
  classical
  exact seeds ∪ seeds.image (·⁻¹)

/-- The routing alphabet is closed under reversing a step. -/
theorem routingGenerators_inv (s : Orderˣ) (hs : s ∈ routingGenerators) :
    s⁻¹ ∈ routingGenerators := by
  classical
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_left _ (by simpa using ht)

/-- Every routing letter acts on all levels of the congruence cover. -/
theorem routingGenerators_mem (s : Orderˣ) (hs : s ∈ routingGenerators) : s ∈ gamma 1 := by
  classical
  have base (t : Orderˣ) (ht : t ∈ seeds) : t ∈ gamma 1 := by
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
      exact (liftFirst r).property
    · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      exact gamma_le_one (p.1.val+1) (liftBase p.1 p.2).property
  rcases Finset.mem_union.mp hs with h | h
  · exact base _ h
  · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    exact (gamma 1).inv_mem (base _ ht)

private theorem base_words (d : ℕ) (hd : d ≤ 1) (i : Fin 3) (t : ZMod 7) :
    ∃ x : gamma (d+2), x.val ∈ routingGenerators ∧ (leading (d+1) x).toAdd = axis i t := by
  classical
  let k : Fin 2 := ⟨d, by omega⟩
  let r := axis i t
  refine ⟨liftBase k r, Finset.mem_union_left _ (Finset.mem_union_right _ ?_), ?_⟩
  · exact Finset.mem_image.mpr ⟨(k,r), Finset.mem_univ _, rfl⟩
  · exact congrArg Multiplicative.toAdd (leading_surj d (.ofAdd r)).choose_spec

private theorem correct_first (g : gamma 1) :
    ∃ s : Orderˣ, HasWord routingGenerators 1 s ∧ s⁻¹*g.val ∈ gamma 2 := by
  classical
  let r := (leading 0).rangeRestrict g
  let s := liftFirst r
  have h : leading 0 s = leading 0 g :=
    congrArg Subtype.val ((leading 0).rangeRestrict_surjective r).choose_spec
  have hn := ((leading 0).eq_iff.mp h.symm)
  rw [leading_kernel] at hn
  refine ⟨s.val, HasWord.single (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)), hn⟩
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩

private theorem correct_layer (d : ℕ) (g : gamma (d+2)) :
    ∃ x : gamma (d+2), HasWord routingGenerators (3*(d+1)^2) x.val ∧
      x.val⁻¹ * g.val ∈ gamma (d+3) := by
  let r := (leading (d+1) g).toAdd
  obtain ⟨a,ha,la⟩ := axis_word _ routingGenerators_inv base_words d 0 r.1
  obtain ⟨b,hb,lb⟩ := axis_word _ routingGenerators_inv base_words d 1 r.2.1
  obtain ⟨c,hc,lc⟩ := axis_word _ routingGenerators_inv base_words d 2 r.2.2
  refine ⟨a*b*c, ?_, ?_⟩
  · exact ((ha.mul hb).mul hc).mono (by omega)
  · have he : leading (d+1) g = leading (d+1) (a*b*c) := by
      apply Multiplicative.toAdd.injective
      simp only [(leading (d+1)).map_mul]
      change r = ((leading (d+1) a).toAdd + (leading (d+1) b).toAdd) +
        (leading (d+1) c).toAdd
      rw [la,lb,lc]
      simp [axis]
    have h := (leading (d+1)).eq_iff.mp he
    rw [leading_kernel] at h
    exact h

/-- Successive residue corrections produce a word whose product represents the
given element modulo `Γ(d+2)`, of length at most `1 + 3*d^3`. -/
theorem routing_word (d : ℕ) (g : gamma 1) :
    ∃ x : Orderˣ, HasWord routingGenerators (1+3*d^3) x ∧ x⁻¹*g.val ∈ gamma (d+2) := by
  induction d with
  | zero => simpa using correct_first g
  | succ d ih =>
    obtain ⟨x,hx,hr⟩ := ih
    let r : gamma (d+2) := ⟨x⁻¹*g.val,hr⟩
    obtain ⟨y,hy,hs⟩ := correct_layer d r
    have hb : 1 + 3*d^3 + 3*(d+1)^2 ≤ 1 + 3*(d+1)^3 := calc
      _ ≤ 1 + 3*d^3 + 3*(d+1)^2 + (6*d^2+3*d) := Nat.le_add_right ..
      _ = _ := by ring
    refine ⟨x*y.val, (hx.mul hy).mono hb, ?_⟩
    simpa only [mul_inv_rev,mul_assoc] using hs

private theorem lift_word (w : List Orderˣ) (hw : ∀ s ∈ w, s ∈ routingGenerators) :
    ∃ l : List (gamma 1), (∀ s ∈ l, s.val ∈ routingGenerators) ∧
      l.length = w.length ∧ l.prod.val = w.prod := by
  induction w with
  | nil => exact ⟨[], by simp, rfl, rfl⟩
  | cons s w ih =>
    have hs := hw s List.mem_cons_self
    obtain ⟨l,hl,ll,pl⟩ := ih fun t ht => hw _ (List.mem_cons_of_mem s ht)
    refine ⟨(⟨s, routingGenerators_mem s hs⟩ : gamma 1) :: l, ?_, by simp [ll], ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | h
      · exact hs
      · exact hl _ h
    · simp only [List.prod_cons, Subgroup.coe_mul,pl]

/-- Lemma 5.1, the diameter bound in the actual deck quotient. Starting at any
tile, right multiplication by at most `1 + 3*d^3` generators reaches any other
tile at level `d+2`. The same fixed symmetric alphabet serves every level. -/
theorem deck_diameter (d : ℕ) (start target : Deck (d+2)) :
    ∃ w : List (gamma 1), (∀ s ∈ w, s.val ∈ routingGenerators) ∧
      w.length ≤ 1+3*d^3 ∧ start * (w.prod : Deck (d+2)) = target := by
  let Q := QuotientGroup.mk' ((gamma (d+2)).subgroupOf (gamma 1))
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective ((gamma (d+2)).subgroupOf (gamma 1))
    (start⁻¹ * target)
  obtain ⟨x,⟨w,hw,lw,rfl⟩,h⟩ := routing_word d g
  obtain ⟨v,hv,lv,pv⟩ := lift_word w hw
  refine ⟨v,hv,lv ▸ lw,?_⟩
  have he : Q g = Q v.prod := by
    apply Q.eq_iff.mpr
    rw [QuotientGroup.ker_mk']
    change v.prod.val⁻¹*g.val ∈ gamma (d+2)
    rwa [pv]
  change start * Q v.prod = target
  rw [← he,hg,mul_inv_cancel_left]

end Cover

end BorderVNP
end Computability
end OAI
