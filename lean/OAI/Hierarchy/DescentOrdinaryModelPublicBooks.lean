import OAI.Hierarchy.DescentDatedNamedBlock
import OAI.Hierarchy.DescentOrdinaryNamedModel
import OAI.Hierarchy.DescentQuotientSourceOperand

namespace OAI
/-! The public book of the actual one-name ordinary normalization. Each occupied
edge input uses the same retained block in every presentation of the final recipe. -/
namespace Hierarchy.DescentStageEdgeReceipt.OrdinaryModel
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentBundleHistory DescentHostDirectory
open DescentPacking DescentPhysicalOrder DescentHostDegree DescentSixParty.StarKeys DescentSixParty.MarkedWorld
open scoped Classical
noncomputable section
section
set_option quotPrecheck false
variable {F P V : Type} [Field F] [DecidableEq V] {d p R q : ℕ} {bits : P → ℕ}
  {W : MarkedWorld F d P bits} {desc : BitDescription W}
  (hp : 0<p) (hq : 0<q) (dvd : p∣q) (s : WorldShape p R desc)
  (key : W.graph.Site → DescentHostDirectory.Key V) (hub : V → Bool) (k g : ℕ)
  (m : (W.coalesced key hub k g).graph.Edge → ℕ)
  (fit : ∀ e ∈ (W.coalesced key hub k g).core,(W.coalesced key hub k g).graph.width e=m e*q)
  (vs : Equiv.Perm ((W.coalesced key hub k g).pieces q m fit).graph.Site)
  (es : Equiv.Perm ((W.coalesced key hub k g).pieces q m fit).graph.Edge)
local notation "baseNorm" => Normalize.merge W V key hub k g (.split _ q m fit (.done _))
local notation "afterNorm" => (baseNorm).appendNames vs es
private def publicBooksAfter :
    SiteBooks hp (WorldShape.follow hp hq dvd afterNorm (show Normalize.CutsEqual q afterNorm from ⟨rfl,trivial⟩) s)
      (s.coalesced key hub k g) :=
  SiteBooks.trans hp (SiteBooks.rename hp ((s.coalesced key hub k g).pieces m q fit hp hq dvd) vs es)
    (SiteBooks.split hp (s.coalesced key hub k g) m q fit hq dvd)
end

variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d p R : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
    (oldID : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (B : OrdinaryModel he T c H)
local notation "rr" => BitDescription.scannedRows he T
local notation "sel" => scanWorld he T c
local notation "key₀" => B.chart.key he T c
local notation "gain" => gainExponent 20 T.Δ
local notation "n₀" => B.named he T c oldID
local notation "coarse₀" => coalesced (scanWorld he T c) key₀ B.chart.hub T.k gain
set_option quotPrecheck false in
local notation "mult" => repetitions W G (rr).pick (fun _=>T.z) (fun _=>T.unitPos) (rr).fit (rr).pack
  ((rr).profile c) key₀ B.chart.hub T.k gain T.z
set_option quotPrecheck false in
local notation "fit" => repetition_width W G (rr).pick (fun _=>T.z) (fun _=>T.unitPos) (rr).fit (rr).pack
  ((rr).profile c) key₀ B.chart.hub T.k gain T.z B.old B.used (fun _=>dvd_refl T.z)
local notation "si" => B.siteMap he T c
local notation "ed" => B.edgeMap he T c oldID
variable (hp : 0<p) {history : BitDescription (scanWorld he T c)} (shape : WorldShape p R history) (multiple : p∣T.z)
local notation "pre" => shape.coalesced key₀ B.chart.hub T.k gain
private abbrev modelCuts : Normalize.CutsEqual T.z (B.named he T c oldID) := ⟨rfl,trivial⟩
local notation "done" => WorldShape.follow hp T.unitPos multiple n₀ (modelCuts he T c oldID B) shape

def publicBooks : SiteBooks hp done pre :=
  publicBooksAfter hp T.unitPos multiple shape key₀ B.chart.hub T.k gain mult fit si ed

local notation "pub" => publicBooks he T c oldID B hp shape multiple

theorem paid_public (v : (n₀).result.graph.Site) (edge : Incident (coarse₀).graph ((si).symm v))
    (chunk : ℕ) (bounded : (chunk+1)*p≤(coarse₀).graph.width edge.val) (mark : edge.val∈(coarse₀).core) :
    let original : BlockRef p (boundaryWidth (coarse₀).graph ((si).symm v)):=⟨.inl edge,chunk,bounded⟩
    let block:=((pub).atSite v).publicWord original
    ∃j : Fin (mult edge.val), j.val=chunk/(T.z/p) ∧
      block.cableNumber (n₀).result.graph v=some (ed (.inr ⟨⟨edge.val,mark⟩,j⟩),chunk%(T.z/p)) := by
  exact named_split_block hp pre mult T.z fit T.unitPos multiple si ed v edge chunk bounded mark

theorem unmarked_public (v : (n₀).result.graph.Site) (edge : Incident (coarse₀).graph ((si).symm v))
    (chunk : ℕ) (bounded : (chunk+1)*p≤(coarse₀).graph.width edge.val) (mark : edge.val∉(coarse₀).core) :
    let original : BlockRef p (boundaryWidth (coarse₀).graph ((si).symm v)):=⟨.inl edge,chunk,bounded⟩
    let block:=((pub).atSite v).publicWord original
    block.cableNumber (n₀).result.graph v=some (ed (.inl ⟨edge.val,mark⟩),chunk) :=
  named_unsplit_block hp pre mult T.z fit T.unitPos multiple si ed v edge chunk bounded mark

private theorem transfer_ticket {α β : Type} {n : ℕ} (read : α → β) (address : Fin n → β)
    (offset : ℕ) {left right : α} (same : left = right)
    (found : ∃ j : Fin n, j.val = offset ∧ read right = address j) :
    ∃ j : Fin n, j.val = offset ∧ read left = address j := same.symm ▸ found

theorem occupied_paid {Y : MarkedWorld F d P bits} {prior : BitDescription Y} {priorShape : WorldShape p R prior}
    (other : SiteBooks hp done priorShape) (v : (n₀).result.graph.Site)
    (node : (((done).sites v).recipe hp).Node) (arg : Fin ((((done).sites v).recipe hp).arity node))
    (leaf : BlockRef p (boundaryWidth Y.graph (other.home v))) (cable : Incident (coarse₀).graph ((si).symm v))
    (chunk : ℕ) (bounded : (chunk+1)*p≤(coarse₀).graph.width cable.val) (mark : cable.val∈(coarse₀).core)
    (earlier : ((priorShape.sites (other.home v)).recipe hp).operand ((other.atSite v).node node)
      (arg.cast ((other.atSite v).length node))=.inl leaf)
    (original : (((pre).sites ((si).symm v)).recipe hp).operand (((pub).atSite v).node node)
      (arg.cast (((pub).atSite v).length node))=.inl ⟨.inl cable,chunk,bounded⟩) :
    ∃j : Fin (mult cable.val), j.val=chunk/(T.z/p) ∧
      ((other.atSite v).publicWord leaf).cableNumber (n₀).result.graph v=
        some (ed (.inr ⟨⟨cable.val,mark⟩,j⟩),chunk%(T.z/p)) := by
  let inputBlock : BlockRef p (boundaryWidth (coarse₀).graph ((si).symm v)) :=
    ⟨.inl cable,chunk,bounded⟩
  have same := WordBook.occupied_public_eq (other.atSite v) ((pub).atSite v)
    node arg leaf inputBlock earlier original
  exact transfer_ticket (BlockRef.cableNumber (n₀).result.graph v)
    (fun j : Fin (mult cable.val) => some (ed (.inr ⟨⟨cable.val,mark⟩,j⟩),chunk%(T.z/p)))
    (chunk/(T.z/p)) same (paid_public he T c oldID B hp shape multiple v cable chunk bounded mark)

end
end Hierarchy.DescentStageEdgeReceipt.OrdinaryModel

end OAI
