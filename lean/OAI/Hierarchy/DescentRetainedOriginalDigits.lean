import OAI.Hierarchy.DescentPreviousPrimitiveCensus

namespace OAI
/-! # The retained decoder and the preceding stage use the same old primitive address -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentCompiler DescentSIMDLookup
open DescentColonies DescentGL DescentOrdinaryAtomFieldRAM DescentIssuedFallbackPanel
open scoped Classical BigOperators
noncomputable section

private theorem rearranged_donor {m c n d : ℕ} (total : m=n) (width : c=d) (L : DescentGL.Layout m)
    (basis : DescentGL.Layout n) (same : HEq L basis) (fits : c≤ m) (fits' : d≤n)
    (hi : Block c) (lo : Block (m-c)) :
    ((rearrange L).symm (join fits hi lo)).cast (congrArg (fun k:ℕ=>2^k) total)=
    (rearrange basis).symm (join fits' (hi.cast (congrArg (fun k:ℕ=>2^k) width))
      (lo.cast (congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total width)))):=by
  subst n;subst d
  have eqn:L=basis:=eq_of_heq same
  subst basis
  rfl

variable (S : AtomSchedule) {k tail i m c G X : ℕ} (base:S.baseGroups=2^tail) (radix:S.radix=2^k)
variable (total:m=S.groupWidth k tail i+k) (groups:G=S.groupCount i) (blocks:X=2^k)
variable (size:2^m=G*X) (fit:c≤ m) (layout:DescentGL.Layout m)
    {d : ℕ} (cut:c=d) (basis:DescentGL.Layout (S.groupWidth k tail i+k))
    (same:HEq layout basis) (lower:d≤S.groupWidth k tail i+k)
local notation "α" => S.resetInputDigits base radix i
local notation "hcast" => congrArg (fun k:ℕ=>2^k) cut
local notation "lcast" => congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total cut)
set_option quotPrecheck false in
local notation:max "raw" hi:arg lo:arg => (rearrange basis).symm (join lower hi lo)

include same in
/-- The actually moved GL word was split by row-major quotient and remainder in
the preceding archive. Neither an order on sites nor a numbering of their types
is involved in this address equality. -/
theorem moved_position (hi:Block c) (lo:Block (m-c)) :
    let where_:=(finProdFinEquiv.symm (Fin.cast size ((rearrange layout).symm (join fit hi lo))):Fin G×Fin X)
    (where_.1.cast groups,where_.2.cast blocks)=α (raw (hi.cast hcast) (lo.cast lcast)):=by
  intro pos
  have donor:=rearranged_donor total cut layout basis same fit lower hi lo
  apply finProdFinEquiv.injective
  apply Fin.ext
  have left:(finProdFinEquiv (pos.1.cast groups,pos.2.cast blocks)).val=
      ((rearrange layout).symm (join fit hi lo)).val:=by
    have casts {a b a' b' : ℕ} (ha : a=a') (hb : b=b') (v : Fin a×Fin b) :
        (finProdFinEquiv (v.1.cast ha,v.2.cast hb)).val=(finProdFinEquiv v).val:=by
      subst a';subst b';rfl
    exact (casts groups blocks pos).trans (congrArg Fin.val ((finProdFinEquiv : Fin G×Fin X≃Fin (G*X)).apply_symm_apply
      (Fin.cast size ((rearrange layout).symm (join fit hi lo)))))
  have right (y:Block (S.groupWidth k tail i+k)):(finProdFinEquiv (α y)).val=y.val:=by
    simp [AtomSchedule.resetInputDigits,finCongr,Nat.mod_add_div]
  exact left.trans ((congrArg Fin.val donor).trans (right _).symm)

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
