import OAI.Hierarchy.DescentOrdinaryMaterialParent
import OAI.Hierarchy.DescentOrdinaryMaterialSocket
import OAI.Hierarchy.DescentOrdinaryRankKeys

namespace OAI
/-! Rebase a single original parent into the true receiving rack while retaining its two rooted endpoints. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route
open DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase.ParentFilter
open DescentOrdinaryDonorSources
open scoped Classical Fin.CommRing
noncomputable section
variable {H D Q K L b regions G B : ℕ}
local notation "P₀" => breadth D
variable (R : Fin H→Fin D→Option (Fin H)) (pitch : ℕ) (positive : 0<pitch) (inside : pitch≤Q)
variable (room : Fused.capacity D Q K L≤2^b) (p : Fin (breadth D)) (x : Fin B)
variable (source : Fin H→Fin (G*B)→Option (Source (breadth D) Q K L))

def fromDonor (h : Fin regions) (g : Fin G) : Option (Fused.Raw R Q K L b) :=
  (receiver H pitch h).bind (fun home=>
    (Gather.select (Gather.reaching R) home p).bind (fun donor=>
      (source donor (finProdFinEquiv (g,x))).map (fun parent=>
        let site : Fin H×Fin Q :=(home,⟨h.val%pitch,(Nat.mod_lt _ positive).trans_le inside⟩)
        ⟨site,p,donor,parent,fun i=>Fused.field_room R site p donor parent i room⟩)))


def atPort (d : Option (Fused.Raw R Q K L b)) (f : Port) : Cell b :=
  ![(PathKeys.selectedPath d false:ℕ),(PathKeys.selectedPath d true:ℕ),PathKeys.issuedPath d,
    (material R d 0).val,(material R d 1).val,(material R d 2).val,(material R d 3).val,
    (material R d 4).val,(material R d 5).val] f

theorem from_original (low : ℕ) (h : Fin regions) (g : Fin G) (f : Port) :
    value R pitch p f x (fun s j=>parentDigits (b:=b) low (source s j) (donorField f)) h g=atPort R (fromDonor R pitch positive inside room p x source h g) f :=by
  have big: 1<2^b:=by unfold Fused.capacity at room;omega
  cases home:receiver H pitch h with
  | none=>fin_cases f <;> simp [value,selected,fromDonor,home,atPort,PathKeys.selectedPath,PathKeys.issuedPath,material]
  | some v=>
    cases got:Gather.select (Gather.reaching R) v p with
    | none=>fin_cases f <;> simp [value,selected,fromDonor,home,got,atPort,PathKeys.selectedPath,PathKeys.issuedPath,material]
    | some d=>
      cases pulled:source d (finProdFinEquiv (g,x)) with
      | none=>fin_cases f <;> simp [value,selected,fromDonor,home,got,pulled,parentDigits,gated,atPort,
            PathKeys.selectedPath,PathKeys.issuedPath,material]
      | some parent=>
        have nonzero : b≠0 := fun eqn => by simp [eqn] at big
        have trim (n : ℕ) : ((n % 2^b : ℕ) : Cell b) = (n : Cell b) := by
          apply Fin.ext
          change n % 2^b % 2^b = n % 2^b
          exact Nat.mod_mod _ _
        fin_cases f <;> simp [value,selected,fromDonor,home,got,pulled,parentDigits,donorField,gated,
          nonzero,trim,stamp,atPort,PathKeys.selectedPath,PathKeys.issuedPath,material]

theorem from_original_location (h : Fin regions) (g : Fin G) {z : Fused.Raw R Q K L b}
    (read : fromDonor R pitch positive inside room p x source h g=some z) : receiver H pitch h=some z.receiver.1 ∧
      Gather.select (Gather.reaching R) z.receiver.1 z.path=some z.host :=by
  cases home:receiver H pitch h with
  | none=>simp [fromDonor,home] at read
  | some v=>
    cases got:Gather.select (Gather.reaching R) v p with
    | none=>simp [fromDonor,home,got] at read
    | some d=>
      cases pulled:source d (finProdFinEquiv (g,x)) with
      | none=>simp [fromDonor,home,got,pulled] at read
      | some parent=>
        simp only [fromDonor,home,got,pulled,Option.bind_some,Option.map_some,Option.some.injEq] at read
        subst z
        simp [got]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

end OAI
