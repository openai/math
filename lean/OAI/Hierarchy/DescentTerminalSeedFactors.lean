import OAI.Hierarchy.DescentSeedInternal
import OAI.Hierarchy.DescentTerminalPackedHost

namespace OAI
/-! # Merging original input-site scalar powers and shared terminal row requests -/

namespace Hierarchy.DescentTerminalSeedFactors
open Computability.BorderVNP.Crossing DescentInitialHost DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {geo : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
variable (A : MarkedWorld F geo P bits) (s : ℕ) (retain : A.graph.Site→Bool)

abbrev Atom := (v : A.graph.Site) × Pattern A.graph v
def entry (i : Atom A) := coeff A.graph A.tables i.1 i.2

def countAt (v : A.graph.Site) : (b : Bool)→Histories.SeedChoice A s v b→Pattern A.graph v→ℕ
  | false,_,_=>0
  | true,h,g=>(h g).val

def counts (c : (Histories.seedInternal A s retain).Choice) (q : Atom A) :=
  countAt A s q.1 (retain q.1) (c q.1) q.2

theorem weight (c : (Histories.seedInternal A s retain).Choice) :
    (Histories.seedInternal A s retain).weight c=∏q:Atom A,(entry A q)^(counts A s retain c q) := by
  rw [Fintype.prod_sigma]
  change (∏v,Histories.seedFactor A s v (retain v) (c v))=_
  apply Finset.prod_congr rfl
  intro v _
  have per (b : Bool) (x : Histories.SeedChoice A s v b) :
      Histories.seedFactor A s v b x =
        ∏g : Pattern A.graph v,coeff A.graph A.tables v g ^ countAt A s v b x g := by
    cases b <;> simp [Histories.seedFactor,countAt,censusWeight]
  exact per (retain v) (c v)

theorem block_weight (R : ℕ) (c : (Histories.collect (fun _ : Fin R=>Histories.seedInternal A s retain)).Choice) :
    (Histories.collect (fun _ : Fin R=>Histories.seedInternal A s retain)).weight c=
      ∏q:Atom A,(entry A q)^(∑j:Fin R,counts A s retain (c j) q) := by
  change (∏j,(Histories.seedInternal A s retain).weight (c j))=_
  simp_rw [weight]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun q _=>Finset.prod_pow_eq_pow_sum _ _ _

/-- Keeping original count words separate for the seed blocks avoids
any native addition across copies, while retaining one fixed scalar menu. -/
theorem separate_blocks (R : ℕ) (c : (Histories.collect (fun _ : Fin R=>Histories.seedInternal A s retain)).Choice) :
    (Histories.collect (fun _ : Fin R=>Histories.seedInternal A s retain)).weight c=
      ∏ q : Fin R × Atom A,(entry A q.2)^(counts A s retain (c q.1) q.2) := by
  rw [Fintype.prod_prod_type]
  change (∏j,(Histories.seedInternal A s retain).weight (c j))=_
  exact Finset.prod_congr rfl fun j _=>weight A s retain (c j)

variable {I L : Type} [Fintype I] [Fintype L] {bins : ℕ}

abbrev Keys (I : Type) (bins : ℕ) := I ⊕ Fin bins

def merged (original : I→F) (table : Fin bins→F) : Fin (Fintype.card I+bins)→F :=
  Sum.elim original table ∘ ((Equiv.sumCongr (Fintype.equivFin _) (Equiv.refl _)).trans finSumFinEquiv).symm

abbrev Occurs (n : I→ℕ) (L : Type) := ((q : I) × Fin (n q)) ⊕ L

def request (n : I→ℕ) (localKey : L→Fin bins) :
    Fin (Fintype.card (Occurs n L))→Fin (Fintype.card I+bins) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Equiv.refl _)).trans finSumFinEquiv ∘
    Sum.map Sigma.fst localKey ∘ (Fintype.equivFin _).symm

theorem requests_product (original : I→F) (table : Fin bins→F) (n : I→ℕ) (localKey : L→Fin bins) :
    (∏t,merged original table (request n localKey t))=
      (∏q,original q^n q)*(∏j,table (localKey j)) := by
  rw [←(Fintype.equivFin (Occurs n L)).prod_comp]
  simp only [request,merged,Function.comp_apply,Equiv.symm_apply_apply,Fintype.prod_sum_type,
    Fintype.prod_sigma,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem bin_count (n : I→ℕ) (localKey : L→Fin bins) (q : I) :
    (Finset.univ.filter (fun z : Fin (Fintype.card (Occurs n L))=> request n localKey z=
      finSumFinEquiv (.inl (Fintype.equivFin I q)))).card=n q := by
  let enc := (Equiv.sumCongr (Fintype.equivFin I) (Equiv.refl (Fin bins))).trans finSumFinEquiv
  let e : Fin (n q) ≃ {z : Fin (Fintype.card (Occurs n L))//request n localKey z=enc (.inl q)} := Equiv.ofBijective
    (fun j=>⟨Fintype.equivFin _ (Sum.inl ⟨q,j⟩),by simp [request,enc]⟩) (by
      constructor
      · intro i j h
        have eq:=(Fintype.equivFin (Occurs n L)).injective (congrArg Subtype.val h)
        simpa using eq
      · rintro ⟨z,hz⟩
        obtain ⟨a,rfl⟩:=(Fintype.equivFin (Occurs n L)).surjective z
        cases a with
        | inl a=>
          rcases a with ⟨i,t⟩
          have same:i=q := by
            apply Sum.inl.inj (β:=Fin bins)
            apply enc.injective
            simpa only [request,enc,Function.comp_apply,Equiv.symm_apply_apply,Sum.map_inl] using hz
          subst i
          exact ⟨t,rfl⟩
        | inr a=>
          have impossible:Sum.inr (α:=I) (localKey a)=.inl q := by
            apply enc.injective
            simpa only [request,enc,Function.comp_apply,Equiv.symm_apply_apply,Sum.map_inr] using hz
          contradiction)
  simpa only [enc,Fintype.card_subtype,Fintype.card_fin,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl]
    using (Fintype.card_congr e).symm

theorem local_count (n : I→ℕ) (localKey : L→Fin bins) (q : Fin bins) :
    (Finset.univ.filter (fun z : Fin (Fintype.card (Occurs n L))=>request n localKey z=finSumFinEquiv (.inr q))).card=
      (Finset.univ.filter (fun j=>localKey j=q)).card := by
  let enc := (Equiv.sumCongr (Fintype.equivFin I) (Equiv.refl (Fin bins))).trans finSumFinEquiv
  let e : {j : L // localKey j=q} ≃ {z : Fin (Fintype.card (Occurs n L)) // request n localKey z=enc (.inr q)} :=
    Equiv.ofBijective
      (fun j=>⟨Fintype.equivFin _ (Sum.inr j.val),by
        simp [enc,request,j.property]⟩) (by
        constructor
        · intro i j eq
          exact Subtype.ext (Sum.inr.inj ((Fintype.equivFin (Occurs n L)).injective (congrArg Subtype.val eq)))
        · rintro ⟨z,hz⟩
          obtain ⟨a,rfl⟩:=(Fintype.equivFin (Occurs n L)).surjective z
          cases a with
          | inr a=>
            have e : Sum.inr (α:=I) (localKey a)=.inr q := by
              apply enc.injective
              simpa only [request,enc,Function.comp_apply,Equiv.symm_apply_apply,Sum.map_inr] using hz
            exact ⟨⟨a,Sum.inr.inj e⟩,rfl⟩
          | inl a=>
            have absurd : Sum.inl (β:=Fin bins) a.1=.inr q := by
              apply enc.injective
              simpa only [request,enc,Function.comp_apply,Equiv.symm_apply_apply,Sum.map_inl] using hz
            contradiction)
  simpa only [enc,Fintype.card_subtype,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,Equiv.refl_apply]
    using (Fintype.card_congr e).symm

end
end Hierarchy.DescentTerminalSeedFactors

end OAI
