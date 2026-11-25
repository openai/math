import OAI.Computability.NearSquareRoot.InterchangeSupport
import OAI.Computability.NearSquareRoot.InterchangeSupportedToken

/-!
# One instruction radix for dense and triangular physical supports

The legal program stored for each change acts at every field width. Its
permutation on the entire pair of address tapes specializes the full rational
change. In particular rational identities among different support choices
remain valid after choosing the radix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Support

open IntegerMultiplication.Port Matrix NearSquareRoot.InterchangeStageLift

variable {J : Type} [DecidableEq J] [Fintype J] {rank : J → ℕ}

def Runs {b : ℕ} (rank : J → ℕ) (cost : ℕ)
    (P : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f)) : Prop :=
  ∃ ops : List (Lag J b), (∀ op ∈ ops, op.legal rank) ∧
    (ops.map Lag.prices).sum ≤ cost ∧ ∀ f x, ops.foldl (Lag.fire f) x = P f x

private theorem address_isUnit {d : ℕ} (F : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ)) :
    IsUnit (addressMatrix F) :=
  ⟨⟨addressMatrix F, addressMatrix F.symm, addressMatrix_inv_mul F.symm, addressMatrix_inv_mul F⟩,rfl⟩

/-- Select all the rational instructions, including both directions of every
support chart, before choosing the radix. -/
theorem compile_pieces {T : Type*} [Fintype T] (P : T → Piece J rank)
    (hrank : Function.Injective rank) (W : ℕ) (extra : Finset ℚ) :
    ∃ b, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ q ∈ extra, (code q = none ↔ q = 0) ∧ ∀ f, Token q ((code q).stamp f)) ∧
      ∀ t, ∃ E : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f),
        (∀ f, AddressToken (coordinateAddress (P t).address) (coordinateAddress (E f))) ∧
        Runs rank (P t).price E := by
  classical
  let coeff := Finset.univ.biUnion fun t => addressCoefficients (P t).change
  obtain ⟨b,hb,hW,code,hcode,hprog⟩ :=
    compile_dependent_matrix_family W (extra ∪ coeff) (fun t => addressMatrix (P t).change)
      (fun t => address_isUnit _)
  refine ⟨b,hb,hW,code,fun q hq => hcode q (Finset.mem_union_left _ hq),fun t => ?_⟩
  let a := P t
  have hC (q) (hq : q ∈ addressCoefficients a.change) :=
    hcode q (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hq⟩))
  let C (f : ℕ) := addressCoefficients_tokens a.change (fun q => (code q).stamp f)
    fun q hq => (hC q hq).2 f
  let F (f : ℕ) := specializeAddress a.change (C f).1 (C f).2
  have ht (f : ℕ) : AddressToken a.change (F f) := specializeAddress_token _ _ _
  refine ⟨fun f => linearEquiv a.slot (F f),fun f => (ht f).supported a.slot,?_⟩
  suffices hc : CompilesOn a.slot rank a.price (fun f => addressMatrix (F f)) by
    obtain ⟨ops,legal,price,effect⟩ := hc
    refine ⟨ops,legal,price,fun f x => ?_⟩
    apply eq_update
    · intro i
      change hear (ops.foldl (Lag.fire f) x) (a.slot i) = (F f) (fun j => hear x (a.slot j)) i
      simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using (effect f x).1 i
    · exact (effect f x).2
  by_cases hfree : a.free = true
  · rw [Piece.price,ite_eq_left hfree]
    exact compile_unitLower rank a.slot (a.ordered hfree) code (addressMatrix a.change)
      (a.lower hfree) (a.diagonal hfree) _ (fun f => (ht f).forward) fun i j f =>
        (hC _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))).2 f
  · obtain ⟨M,hM,hc⟩ := hprog t
    have H : M = fun f => addressMatrix (F f) := funext fun f => (hM f).unique (ht f).forward
    simpa only [H,Piece.price,ite_eq_right hfree,Fintype.card_fin] using
      hc a.slot a.slot.injective rank hrank

namespace Runs

variable {b : ℕ} {k l : ℕ} {P Q : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f)}

omit [Fintype J] in
theorem refl : Runs (b := b) rank 0 (fun _ => .refl _ _) := ⟨[],by simp,by simp,by simp⟩

omit [Fintype J] in
theorem trans (hp : Runs rank k P) (hq : Runs rank l Q) :
    Runs rank (k+l) (fun f => (P f).trans (Q f)) := by
  obtain ⟨p,hp,cp,ep⟩ := hp
  obtain ⟨q,hq,cq,eq⟩ := hq
  exact ⟨p++q,fun u hu => (List.mem_append.mp hu).elim (hp u) (hq u),
    by simpa using Nat.add_le_add cp cq,by simp [ep,eq]⟩

omit [Fintype J] in
theorem symm (hP : Runs rank k P) : Runs rank k (fun f => (P f).symm) := by
  obtain ⟨p,hp,cp,ep⟩ := hP
  refine ⟨p.reverse.map Lag.rewind,fun op hop => ?_,?_,fun f x => ?_⟩
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hop
    exact Lag.rewind_legal _ u (hp u (List.mem_reverse.mp hu))
  · have H : Lag.prices ∘ (Lag.rewind (J := J) (p := b)) = Lag.prices := by
      funext op; cases op <;> rfl
    simpa only [List.map_map,H,List.map_reverse,List.sum_reverse] using cp
  · have H := Lag.backlist f ((P f).symm x) p rank hp
    simpa [ep] using H

end Runs

namespace Word

noncomputable def atoms (w : Word J rank) : Finset (Piece J rank) := by
  classical
  exact match w with
  | .idle => ∅
  | .atom p => {p}
  | .seq u v => u.atoms ∪ v.atoms
  | .symm u => u.atoms

private theorem by_atoms {b : ℕ} (w : Word J rank)
    (h : ∀ a ∈ w.atoms, ∃ E : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f),
      (∀ f, AddressToken (coordinateAddress a.address) (coordinateAddress (E f))) ∧ Runs rank a.price E) :
    ∃ E : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f),
      (∀ f, AddressToken (coordinateAddress w.address) (coordinateAddress (E f))) ∧ Runs rank w.price E := by
  classical
  induction w with
  | idle =>
    refine ⟨_,fun f => ?_,Runs.refl⟩
    have h₀ {R : Type} [CommRing R] :
        coordinateAddress (.refl R (Duplex J R)) = .refl R _ := by
      apply LinearEquiv.ext
      intro x
      simp [coordinateAddress]
    simpa only [address,h₀] using (AddressToken.refl (I := Spot J) (R := Tower b f))
  | atom a => exact h a (by simp [atoms])
  | seq u v ih jh =>
    obtain ⟨F,hF,pF⟩ := ih (fun a ha => h a (Finset.mem_union_left _ ha))
    obtain ⟨G,hG,pG⟩ := jh (fun a ha => h a (Finset.mem_union_right _ ha))
    exact ⟨_,fun f => by simpa only [address,coordinateAddress_trans] using (hF f).trans (hG f),pF.trans pG⟩
  | symm u ih =>
    obtain ⟨F,hF,pF⟩ := ih h
    exact ⟨_,fun f => by simpa only [address,coordinateAddress_symm] using (hF f).symm,pF.symm⟩

end Word

/-- All words in a fixed routing stage have one common prime and issue one
width-independent instruction list each. Their specialized address maps
respect all equalities of the original rational changes. -/
theorem compile_words {T : Type*} [Fintype T] (w : T → Word J rank)
    (hrank : Function.Injective rank) (W : ℕ) (extra : Finset ℚ) :
    ∃ b, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ q ∈ extra, (code q = none ↔ q = 0) ∧ ∀ f, Token q ((code q).stamp f)) ∧
      ∀ t, ∃ E : (f : ℕ) → Duplex J (Tower b f) ≃ₗ[Tower b f] Duplex J (Tower b f),
        (∀ f, AddressToken (coordinateAddress (w t).address) (coordinateAddress (E f))) ∧
        Runs rank (w t).price E := by
  classical
  let catalog := Finset.univ.biUnion fun t => (w t).atoms
  obtain ⟨b,hb,hW,code,hcode,hp⟩ := compile_pieces (fun x : catalog => x.val) hrank W extra
  refine ⟨b,hb,hW,code,hcode,fun t => (w t).by_atoms fun a ha =>
    hp ⟨a,Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,ha⟩⟩⟩

end Interchange.Support

end NearSquareRoot
end Computability
end OAI
