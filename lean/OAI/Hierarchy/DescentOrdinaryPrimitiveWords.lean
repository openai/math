import OAI.Hierarchy.DescentPrimitiveAtNode
import OAI.Hierarchy.DescentNormalizedPalette
import OAI.Hierarchy.DescentLocalNodeOwners

namespace OAI
/-! # The retained coefficient word and true profile/role word at a paid ordinary node -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler
open scoped Classical
noncomputable section
variable {F P U : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {read : U→List (List Bool)→F} {G : PoweredGadget F}


theorem Encoding.transport_at {W' : MarkedWorld F d P bits} (h : W=W') {B : BitDescription W} (e : Encoding U read B)
    (x : NodeOrder.All (cast (congrArg BitDescription h) B)) :
    (Encoding.transport h e).atNode x=e.atNode (NodeOrder.castNames h B x) := by subst W';rfl

theorem Encoding.follow_at {B : BitDescription W} (e : Encoding U read B) (n : Normalize W)
    (x : NodeOrder.All (B.follow n)) :
    (e.follow n).atNode x=e.atNode (NodeOrder.followNames n B x) := by
  induction n with
  | done=>rfl
  | split W q m fit rest ih=>
    exact @ih (B.pieces m q fit) ⟨e.code,e.correct⟩ x
  | named W s t rest ih=>
    exact @ih (B.renamed s t) ⟨e.code,e.correct⟩ x
  | merge W V key flag k g rest ih=>
    exact @ih (B.coalesced (V:=V) key flag k g) ⟨e.code,e.correct⟩ x

variable {s Z p : ℕ} (op : RotorSpec) (menu : Runnable F op)
variable {S : AtomSchedule} {k i z D z' D' wire hist : ℕ} {u q ε : ℝ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (a : Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) a.bit) (limit : T.z≤Z)
set_option quotPrecheck false
local notation "r" => BitDescription.scannedRows he T
local notation "sel" => a.bit.selected G (r).pick (fun _=>T.z) (fun _=>T.unitPos) (r).fit (fun _=>le_refl T.z)
  (r).pack ((r).profile c)
local notation "nm" => NodeOrder.selectedNames a.bit G (r).pick (fun _=>T.z) (fun _=>T.unitPos) (r).fit (fun _=>le_refl T.z)
  (r).pack ((r).profile c)
local notation "post" => (Encoding.scanned G op menu old T he c limit).follow n

def bornLabel (i : (r).pairs) (j : Fin 6) : Label G s Z op :=
  .inr (.inl (⟨T.z,Nat.lt_succ_of_le limit⟩,(r).profile c i,j))

set_option maxHeartbeats 800000 in
theorem ordinary_at (x : NodeOrder.All (ticket.advance a).bit) :
    (post).atNode x=Sum.elim old.atNode (fun ij=>bornLabel (s:=s) op (c:=c) limit ij.1 ij.2) (roots ticket a x) := by
  refine (Encoding.follow_at (Encoding.scanned G op menu old T he c limit) n x).trans ?_
  let start:=NodeOrder.followNames n _ x
  let raw:=NodeOrder.castNames ((r).state c).symm _ start
  unfold Encoding.scanned
  erw [Encoding.transport_at]
  let encode : (a.bit.Tag ⊕ GadgetTag G T.z) → Label G s Z op :=
    Sum.elim old.code (fun tag => Sum.inr (Sum.inl (promote G limit tag)))
  let readSelected (z : NodeOrder.All sel) := encode (((sel).recipe z.1).tag z.2)
  change readSelected raw=Sum.elim _ _ ((nm) raw)
  have evaluate (o : NodeOrder.All a.bit ⊕ (r).pairs×Fin 6) : readSelected ((nm).symm o)=Sum.elim old.atNode
      (fun ij=>bornLabel (s:=s) op (c:=c) limit ij.1 ij.2) o := by
    rcases o with u|⟨i,j⟩
    · exact congrArg encode (NodeOrder.selected_tag_old a.bit G (r).pick (fun _=>T.z)
        (fun _=>T.unitPos) (r).fit (fun _=>le_refl T.z) (r).pack ((r).profile c) u)
    · exact congrArg encode (NodeOrder.selected_tag_born a.bit G (r).pick (fun _=>T.z)
        (fun _=>T.unitPos) (r).fit (fun _=>le_refl T.z) (r).pack ((r).profile c) i j)
  exact (congrArg readSelected ((nm).symm_apply_apply raw).symm).trans (evaluate ((nm) raw))

theorem ordinary_word (x : NodeOrder.All (ticket.advance a).bit) :
    ((codec (G:=G) op).store ((post).atNode x)).val=Sum.elim
      (fun z=>((codec (G:=G) op).store (old.atNode z)).val)
      (fun ij=>censusCount s+((DescentEpochTagKeys.gadget Z G.C).store
        (⟨T.z,Nat.lt_succ_of_le limit⟩,(r).profile c ij.1,ij.2)).val) (roots ticket a x) := by
  rw [ordinary_at op menu ticket a old limit]
  cases roots ticket a x <;> rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
