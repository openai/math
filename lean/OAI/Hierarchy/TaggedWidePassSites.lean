import OAI.Hierarchy.TaggedWirePassMatrix
import OAI.Hierarchy.TaggedWideSiteModes
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # One fixed packet evaluator per site of an actual disjoint repair pass -/
noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing
open scoped Classical BigOperators
variable {F V K : Type} [Field F] [Fintype V] [Fintype K] {S n bits : ℕ}
    {J : Fin n → Type} [∀i,Fintype (J i)]
    {demand : Fin n → Widths S} {installed : ∀i,J i → Widths S}
    (M : ∀i c,SiteMatrix (State (demand i)) (State (installed i c)) F)

/-- A permanent finite family of LUT formats is installed once at a
physical site. Its changing row, histogram and site within the strip are
observed at this site's RAM addresses. The idle code is included in K. -/
def siteNet (carry : BitNetwork F (Fintype.card V)) (body : K → BitNetwork F (Fintype.card V))
    (mode : Fin bits → V) (tags : K ↪ (Fin bits → Bool)) : BitNetwork F (Fintype.card V) :=
  Tagged.WideHost.localFamily (V:=V) (A:=fun _ : Option K=>V)
    (fun k=>k.elim carry (fun k=>Tagged.Guard.mode (body k) mode (tags k))) (fun _=>Sum.inl)

theorem site_fee (carry : BitNetwork F (Fintype.card V)) (body : K → BitNetwork F (Fintype.card V))
    (mode : Fin bits → V) (tags : K ↪ (Fin bits → Bool)) :
    (siteNet carry body mode tags).cells+(siteNet carry body mode tags).internal≤
      (carry.cells+carry.internal)+177^bits*∑k,((body k).cells+(body k).internal) := by
  rw [siteNet,Tagged.WideHost.localFamily_size,Fintype.sum_option]
  simp only [Option.elim_none,Option.elim_some,Finset.mul_sum]
  gcongr with k
  exact Tagged.Guard.mode_fee (body k) mode (tags k)

theorem off_routing {a b : Type*} [Fintype b] [Subsingleton b] [Nonempty b]
    (first : a → b → F) (second : b → F) (x : a) (emptyIn : ∀y,first x y=1)
    (emptyOut : ∀y,second y=1) : (∑y,second y*first x y)=1 := by
  classical
  let : Unique b := ⟨⟨Classical.choice ‹Nonempty b›⟩,fun _=>Subsingleton.elim _ _⟩
  simp [emptyIn,emptyOut]

private theorem selected_product {I : Type} [Fintype I] (tile : I→F) (owner : Option I)
    (p : Prop) {gate table : Decidable p} {carry body : F}
    (pass : carry=@ite F p gate 1 0) (active : body=owner.elim 1 tile)
    (away : ∀i,owner≠some i→tile i=1) :
    carry*body=@ite F p table 1 0 * ∏i,tile i := by
  cases Subsingleton.elim gate table
  apply congrArg₂ (·*·) pass
  rw [active]
  cases chosen : owner with
  | none=>symm; exact Finset.prod_eq_one fun i _=>away i (by simp [chosen])
  | some i=>
    symm
    apply Finset.prod_eq_single i
    · intro j _ ne
      exact away j (by simp [chosen,Ne.symm ne])
    · simp

omit [(i : Fin n) → Fintype (J i)] in
/-- The product law is on all native candidates, including zero-width
candidates. Honest disjointness leaves a single factor at each selected
site. Consequently the circuit's size is independent of the global number
of possible centers. -/
theorem site_value (carry : BitNetwork F (Fintype.card V)) (body : K → BitNetwork F (Fintype.card V))
    (mode : Fin bits → V) (tags : K ↪ (Fin bits → Bool))
    (v : V → Bool) (rest : Widths S) (c : ∀i,J i) (s : Fin S)
    (a : State (rest+∑i,demand i) s) (b : State (rest+∑i,installed i (c i)) s)
    (kind : K) (key : v ∘ mode=tags kind) (owner : Option (Fin n))
    (pass : TypedWiring.value carry v=
      if (splitPortState rest (∑i,installed i (c i)) s b).1=(splitPortState rest (∑i,demand i) s a).1
      then 1 else 0)
    (active : let before := blockPortState demand s (splitPortState rest (∑i,demand i) s a).2
      let after := blockPortState (fun i=>installed i (c i)) s (splitPortState rest (∑i,installed i (c i)) s b).2
      TypedWiring.value (body kind) v=owner.elim 1 (fun i=>M i (c i) s (before i) (after i)))
    (away : ∀i,owner≠some i→
      M i (c i) s (blockPortState demand s (splitPortState rest (∑i,demand i) s a).2 i)
        (blockPortState (fun i=>installed i (c i)) s (splitPortState rest (∑i,installed i (c i)) s b).2 i)=1) :
    TypedWiring.value (siteNet carry body mode tags) v=matrix M rest c s a b := by
  rw [siteNet,Tagged.WideHost.localFamily_eval,Fintype.prod_option]
  change TypedWiring.value carry v*(∏i,TypedWiring.value (Tagged.Guard.mode (body i) mode (tags i)) v)=_
  rw [Tagged.Guard.modes_value body mode tags kind v key]
  let before := splitPortState rest (∑i,demand i) s a
  let after := splitPortState rest (∑i,installed i (c i)) s b
  let tile : Fin n→F := fun i=>M i (c i) s (blockPortState demand s before.2 i)
    (blockPortState (fun i=>installed i (c i)) s after.2 i)
  unfold matrix productTable tiles tiledTable SiteMatrix.identity
  exact selected_product tile owner (after.1=before.1) pass active away

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
