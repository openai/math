import OAI.Hierarchy.DescentOrdinaryAtomVenueRead
import OAI.Hierarchy.DescentLocalArchiveOrder

namespace OAI
/-! # The compact donor book has the canonical local comparison -/
namespace Hierarchy.DescentOrdinaryLocalBirth
open DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing DescentNetworkPartition
open DescentCableDonorNames DescentSharedCableNames DescentLocalArchiveOrder
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C] {d k i D K Z d₁ d₂ : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (desc : BitDescription W) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (room : ∀i,z i≤Z) (prof : I→Profile G.C) (picked : ∀i,pick (i,0)∈W.core)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
local notation "r₀" => physicalBits G W.toWorld pick z room prof desc.recipe
variable (a : GadgetNetwork.Site (I:=I) W.graph→T) (b : T→C)
variable (x₁ : T→EuclideanSpace ℝ (Fin d₁)) (x₂ : C→EuclideanSpace ℝ (Fin d₂))
    (ok₁ : ∀t,‖x₁ t‖≤1) (ok₂ : ∀t,‖x₂ t‖≤1)
local notation "mid" => quotient M a x₁ ok₁
local notation "r₁" => quotientBits M a x₁ ok₁ r₀
local notation "r₂" => quotientBits mid b x₂ ok₂ r₁
local notation "loc" => (b∘a)
variable (halo : Halo C W.graph.Site D)
    (oldHere : ∀u : W.graph.Site,u∈halo.member (b (a (.inl u))))
    (newHere : ∀i j,W.graph.src (pick (i,0))∈halo.member (b (a (.inr (i,j)))))
    (oldRank : ∀u,(desc.recipe u).Node ↪ Fin K)
variable (site : W.graph.Site↪Fin (Fintype.card W.graph.Site)) (prior : Local desc)
    (ordered : ∀c (x y : ↥(halo.member c)),halo.slot c x<halo.slot c y ↔ site x.val<site y.val)
    (oldRead : ∀u n,(oldRank u n).val=(prior u n).val)
variable (c : C)
local notation "Roster" => Σt : {t : GadgetNetwork.Site (I:=I) W.graph //loc t=c},(r₀ t.val).Node

def origin : Roster → NodeOrder.All desc ⊕ (I×Fin 6)
  | ⟨⟨.inl u,_⟩,n⟩=>.inl ⟨u,n⟩
  | ⟨⟨.inr ij,_⟩,_⟩=>.inr ij

def donor : Roster → ↥(halo.member c)
  | ⟨⟨.inl u,h⟩,_⟩=>⟨u,h ▸ oldHere u⟩
  | ⟨⟨.inr (i,j),h⟩,_⟩=>⟨W.graph.src (pick (i,0)),h ▸ newHere i j⟩

local notation "source" => origin desc pick z room prof a b c
local notation "locate" => donor desc pick z room prof a b halo oldHere newHere c
local notation "bk" => book A native S ready desc pick z room prof picked a b halo oldHere newHere oldRank c
local notation "eqnFields" => donorEntry A native S ready desc prior pick picked site

private theorem product_lt {H L : ℕ} (x y : Fin H×Fin L) :
    finProdFinEquiv x<finProdFinEquiv y ↔ x.1<y.1 ∨ x.1=y.1 ∧ x.2<y.2 := by
  simpa only [Fin.lt_def,Fin.ext_iff,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using
    (DescentCableDonorNames.digit_lt (a:=x.1.val) (b:=y.1.val) x.2.isLt y.2.isLt)

include ordered oldRead in
omit [Fintype T] [Fintype C] in
theorem book_compare (x y : Roster) :
    bk x<bk y ↔ donorKey A native S ready desc prior pick picked site (source x) <
      donorKey A native S ready desc prior pick picked site (source y) := by
  let lhs (x : Roster) := finProdFinEquiv.symm (bk x)
  let rhs (x : Roster) := eqnFields (source x)
  have left (x : Roster) : (lhs x).1=halo.slot c (locate x) := by
    rcases x with ⟨⟨u|⟨u,j⟩,h⟩,n⟩ <;>
      change ((finProdFinEquiv (m:=D) (n:=K+A.cap*6)).symm (finProdFinEquiv _)).1 = _ <;>
      rw [Equiv.symm_apply_apply] <;> rfl
  have right (x : Roster) : (rhs x).1=site (locate x).val := by
    rcases x with ⟨⟨u|⟨u,j⟩,h⟩,n⟩ <;> rfl
  have tail : (lhs x).2<(lhs y).2 ↔ (rhs x).2<(rhs y).2 := by
    have bound (v : W.graph.Site) (n : (desc.recipe v).Node) :
        (prior v n).val<K ∧ (prior v n).val< maxNodes desc :=
      ⟨(oldRead v n) ▸ (oldRank v n).isLt,(bounded desc prior v n).isLt⟩
    rcases x with ⟨⟨v|⟨i,j⟩,hv⟩,n⟩ <;> rcases y with ⟨⟨v'|⟨i',j'⟩,hv'⟩,n'⟩
    all_goals simp only [lhs,rhs,origin,book,donorEntry,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply,
      Fin.lt_def,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
      bounded,Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
    · change (oldRank v n).val < (oldRank v' n').val ↔ (prior v n).val < (prior v' n').val
      rw [oldRead v n,oldRead v' n']
    · have h:=bound v n;omega
    · have h:=bound v' n';omega
    · omega
  have same : (lhs x).1=(lhs y).1 ↔ (rhs x).1=(rhs y).1 := by
    rw [left,left,right,right,(halo.slot c).injective.eq_iff,site.injective.eq_iff,Subtype.ext_iff]
  have less : (lhs x).1<(lhs y).1 ↔ (rhs x).1<(rhs y).1 := by
    rw [left,left,right,right];exact ordered c _ _
  calc
    bk x<bk y ↔ finProdFinEquiv (lhs x)<finProdFinEquiv (lhs y) := by simp only [lhs, Equiv.apply_symm_apply]
    _ ↔ finProdFinEquiv (rhs x)<finProdFinEquiv (rhs y) := by rw [product_lt,product_lt,less,same,tail]
    _ ↔ _ := Iff.rfl

include ordered oldRead in
theorem compact_source_read (u : (r₂ c).Node) :
    let orig:=source ∘ roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c
    let name:=donorKey A native S ready desc prior pick picked site
    (compact A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c u).val=
      (Finset.univ.filter (fun v=>name (orig v)<name (orig u))).card := by
  rw [compact_read]
  congr 1
  apply Finset.filter_congr
  intro v _
  exact book_compare A native S ready desc pick z room prof picked a b halo oldHere newHere oldRank site prior ordered oldRead c _ _

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI
