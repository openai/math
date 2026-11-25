import OAI.Hierarchy.DescentOrdinaryMaterialRaw
import OAI.Hierarchy.DescentOrdinaryParentShelf

namespace OAI
/-! The actual original rack/seat is the address used by the normalized parent roster on both receiving faces. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route
open DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open scoped Classical
noncomputable section
variable {U E T V : Type} [Fintype U] [DecidableEq U] [Fintype E] [Fintype T]
  {n H D Q O K L b G B regions : ℕ} {S : Ends U n} (C : Blocks S E)
  (R : Fin H→Fin D→Option (Fin H))
  (Z : Measured C R (Fin H×Fin O) T V Q O K L) (shelf : Measured.Shelf C R Z)
  (small : ∀h p raw (s : Source (breadth D) Q K L) i,
    Machine.fields R (Z.venue h) p (Z.loc raw).1 s i<2^b)
  (flat : Z.loc=Function.Embedding.refl _)
local notation "P₀" => breadth D
variable (pitch : ℕ) (positive : 0<pitch) (inside : pitch≤Q)
  (room : Fused.capacity D Q K L≤2^b) (p : Fin (breadth D)) (o : Fin O)
  (x : Fin B) (source : Fin H→Fin (G*B)→Option (Source (breadth D) Q K L))
  (which : Fin regions→Fin G→Option U) (h : Fin regions) (g : Fin G)

include flat in
omit [Fintype U] [Fintype E] in
theorem original_shelf
    (occupied : ∀u,which h g=some u→ receiver H pitch h=some (Z.venue u).1 ∧ (Z.venue u).2.val=h.val%pitch)
    (readSeat : ∀u,which h g=some u→∀d,source d (finProdFinEquiv (g,x))=shelf.issued u (d,o))
    (padded : which h g=none→∀v,receiver H pitch h=some v→∀d,
      Gather.select (Gather.reaching R) v p=some d→source d (finProdFinEquiv (g,x))=none) :
    fromDonor R pitch positive inside room p x source h g=
      Fused.cell C R Z shelf small which (finProdFinEquiv (p,o)) h g :=by
  cases active:which h g with
  | none=>
    rw [Fused.cell,active,Option.bind_none]
    cases origin:receiver H pitch h with
    | none=>simp [fromDonor,origin]
    | some v=>
      cases at_:Gather.select (Gather.reaching R) v p with
      | none=>simp [fromDonor,origin,at_]
      | some d=>simp [fromDonor,origin,at_,padded active v origin d at_]
  | some u=>
    obtain ⟨home,low⟩:=occupied u active
    have venue:((Z.venue u).1,(⟨h.val%pitch,(Nat.mod_lt _ positive).trans_le inside⟩:Fin Q))=Z.venue u:=by
      apply Prod.ext
      · rfl
      · exact Fin.ext low.symm
    simp only [Fused.cell,active,Option.bind_some,Fused.fetched,Resident.collected,Equiv.symm_apply_apply,
      fromDonor,home]
    cases peer:Gather.select (Gather.reaching R) (Z.venue u).1 p with
    | none=>rfl
    | some d=>
      have loc : Z.loc (d,o)=(d,o):=by rw [flat];rfl
      have anchor:=Resident.old_at Z.loc (Fused.previous C R Z shelf small u p) (d,o)
      rw [loc] at anchor
      simp only [Option.bind_some,anchor,Fused.previous,readSeat u active,loc]
      cases seen:shelf.issued u (d,o) <;> simp [venue]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

end OAI
