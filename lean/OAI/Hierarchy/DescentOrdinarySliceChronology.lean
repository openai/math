import OAI.Hierarchy.DescentFreshRoleMeasuredFields
import OAI.Hierarchy.DescentBundleSchedule
import OAI.Hierarchy.DescentLocalArchiveOrder

namespace OAI
/-! # Actual immutable slice fields through selected nodes, the true ordinary quotient, and normalization -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {B : BitDescription W}

def WorldShape.nodeFields (s : WorldShape p R B) (x : NodeOrder.All B) := (s.sites x.1).sliceFields x.2

theorem WorldShape.transport_fields {W' : MarkedWorld F d P bits} (h : W=W') (s : WorldShape p R B)
    (x : NodeOrder.All (cast (congrArg BitDescription h) B)) :
    (s.transport h).nodeFields x=s.nodeFields (NodeOrder.castNames h B x) := by subst W';rfl

theorem WorldShape.follow_fields (hp : 0<p) {z:ℕ} (hz:0<z) (divides:p∣z) (n:Normalize W)
    (cuts:Normalize.CutsEqual z n) (s:WorldShape p R B) (x:NodeOrder.All (B.follow n)) :
    (WorldShape.follow hp hz divides n cuts s).nodeFields x=s.nodeFields (NodeOrder.followNames n B x) := by
  induction n with
  | done=>rfl
  | named W a e rest ih=>
    exact ih (B:=B.renamed a e) cuts (s.renamed a e) x
  | merge W V key flag k g rest ih=>
    exact ih (B:=B.coalesced key flag k g) cuts (s.coalesced key flag k g) x
  | split W z' m cut rest ih=>
    obtain ⟨rfl,more⟩:=cuts
    exact ih (B:=B.pieces m z' cut) more (s.pieces m z' cut hp hz divides) x

variable {G : PoweredGadget F} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ} {u q ε : ℝ}
    {cap : Reached W G q ε S k i z D wire hist} {he:0≤ε} {T:StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket:OrdinaryLink cap he T c n target) (a:Archive W) (s:WorldShape p R a.bit)
    (hp:0<p) (one:1≤R) (pins:∀v,p∣bits v) (unit:p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "cut" => ticket.quantum.symm ▸ ticket.cuts
local notation "post" => WorldShape.follow hp T.unitPos unit n cut (WorldShape.scanned he hp one pins T s unit c)
local notation "name" => NodeOrder.selectedNames a.bit G (r).pick (fun _=>T.z) (fun _=>T.unitPos)
  (r).fit (fun _=>le_refl T.z) (r).pack ((r).profile c)
local notation "plan" => s.selected hp one pins G (r).pick (fun _=>T.z) (fun _=>T.unitPos) (r).fit
  (fun _=>le_refl T.z) (r).pack ((r).profile c) (fun _=>unit)
local notation "M" => GadgetNetwork.physical W.graph (r).pick (branchWidth G (fun _=>T.z) ((r).profile c))
local notation "fresh" => fun ij : (r).pairs×Fin 6=>DescentFreshRoleFields.header G p T.z ((r).profile c ij.1) ij.2

/-- The original scalar-book issuer's genuine old-or-fresh choice independently determines all
slice lengths, starts, strides and counts for the very same attained final scalar node. -/
theorem ordinary_fields (x:NodeOrder.All (ticket.advance a).bit) :
    (post).nodeFields x=Sum.elim s.nodeFields fresh (roots ticket a x) := by
  refine (WorldShape.follow_fields hp T.unitPos unit n cut
    (WorldShape.scanned he hp one pins T s unit c) x).trans ?_
  refine (WorldShape.transport_fields ((r).state c).symm plan (NodeOrder.followNames n _ x)).trans ?_
  let raw:=NodeOrder.castNames ((r).state c).symm _ (NodeOrder.followNames n _ x)
  change (plan).nodeFields raw=Sum.elim _ _ (name raw)
  have choose (o:NodeOrder.All a.bit⊕(r).pairs×Fin 6) : (plan).nodeFields ((name).symm o)=Sum.elim s.nodeFields fresh o := by
    rcases o with old|⟨j,role⟩
    · rfl
    · let pub (b : Boundary M (.inr (j,role))) : p∣boundaryWidth M (.inr (j,role)) b := by
        rcases b with e|ex
        · exact physical_multiple W G (r).pick (fun _=>T.z) ((r).profile c) s.edges (fun _=>unit) e.val
        · exact pins ex.val
      have actual:=DescentFreshRoleFields.real_header G W.graph (r).pick (fun _=>T.z) (fun _=>le_refl T.z)
        ((r).profile c) (r).fit hp j role pub (fun h => nomatch h)
      let sh := exposed (roleRecipe G W.graph (r).pick (fun _ => T.z) (fun _ => le_refl T.z)
        ((r).profile c) j role) (boundaryWidth M (.inr (j,role))) hp pub (fun h => nomatch h)
      exact congrArg Prod.snd ((Shape.tag_fields hp sh ()).symm.trans actual)
  simpa using choose (name raw)

end
end Hierarchy.DescentBundleHistory

end OAI
