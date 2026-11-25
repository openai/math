import OAI.Hierarchy.DescentNodeCellRoleCount
import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentPackedSourceAccess
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Live and padded arities in the original metadata word -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentSIMDLookup DescentColonies DescentPackedColony Chronology ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {H N a p R age z D wire hist k:ℕ} {q ε:ℝ} {S:AtomSchedule}
  (r:Reached W G q ε S k age z D wire hist) (B:BitDescription W) (ord:Local B)
  (shape:WorldShape p R B) (hp:0<p) (u:W.graph.Site) (host:Fin H)
  (name:(r.vertex (r.placement.pos u).2).val=host.val)
  (cap:Fintype.card (B.recipe u).Node≤N)
set_option quotPrecheck false in
local notation "atNode" => (ord u).toEmbedding.trans (Fin.castLEEmb cap)
set_option quotPrecheck false in
local notation:max "siteRow" n:arg => atPhysical r B ord (r.placement.block u) (n:Fin N) host (r.placement.pos u).1

include name in
/-- Every occupied slot in this physical group and block belongs to its one selected site. -/
theorem outside_ordinal (n:Fin N) (empty:∀s,atNode s≠n) : siteRow n=none:=by
  cases h:siteRow n with
  | none=>rfl
  | some y=>
    rcases y with ⟨v,s⟩
    obtain ⟨rack,g,b,j⟩:=(atPhysical_some r B ord _ _ _ _ v s).mp h
    have same:v=u:=r.valid.coordinates (Prod.ext (Prod.ext g
      (r.vertex.injective (Fin.ext (rack.trans name.symm)))) b)
    subst v
    exact False.elim (empty s (Fin.ext j.symm))

include name in
/-- The arity scan sees the flattened list of actual slices at every genuine
node and zero at an unused node ordinal, including when this site is unfunded. -/
theorem original_arity_digits (value:Cell (a*N))
    (full:value=encode a N (fun n=>(siteRow n).elim 0 (fun y=>
      ((occurrences (shape.sites y.1) y.2).length:Cell a))))
    (size:∀s,((shape.sites u).recipe hp).arity s<2^a) :
    (∀s,digit a (atNode s).val value.val=((shape.sites u).recipe hp).arity s) ∧
    ∀n:Fin N,(∀s,atNode s≠n)→digit a n.val value.val=0:=by
  rw [full]
  constructor
  · intro s
    have hit:siteRow (atNode s)=some ⟨u,s⟩:=(atPhysical_some r B ord _ _ _ _ u s).2 ⟨name,rfl,rfl,rfl⟩
    rw [digit_encode,hit]
    change (((occurrences (shape.sites u) s).length:Cell a).val)=_
    rw [DescentRetainedRangeDigits.length _ _ hp,Fin.val_natCast,Nat.mod_eq_of_lt (size s)]
  · intro n vacant
    rw [digit_encode,outside_ordinal r B ord u host name cap n vacant]
    rfl

/-- Comparing the two reads at the selected group only requires one packed
row. The last partially occupied group word uses the same address. -/
theorem arity_row_eq {w M:ℕ} (bank:Bank) (m:Memory w) (x y:Fin H→Fin (S.groupCount age)→Cell (a*N))
    (old:Reads bank x M m) (semantic:Reads bank y M m) (pos:0<M) (wide:a*N*M≤w) :
    x host (r.placement.pos u).1=y host (r.placement.pos u).1:=by
  apply Fin.ext
  exact (PackedSource.read x m bank.base pos wide old host (r.placement.pos u).1).symm.trans
    (PackedSource.read y m bank.base pos wide semantic host (r.placement.pos u).1)

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
