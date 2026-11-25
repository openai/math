import OAI.Hierarchy.DescentIssuedPrivateBooks
import OAI.Hierarchy.DescentPrivateBookHalo
import OAI.Hierarchy.DescentOrdinaryPrivateBasis

namespace OAI
/-! # The exact compact operand key of a live private word after the issued ordinary step -/
namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
private theorem wordBook_read_key {A B T U : Type} {left : Recipe T A} {right : Recipe U B}
    (bk : WordBook left right) (key : right.UsedWord ↪ Key) (a : left.Node)
    (j : Fin (left.arity a)) (w : left.UsedWord) :
    left.operand a j = Sum.inr w.val ↔
      ∃ h : right.UsedWord,
        right.operand (bk.node a) (Fin.cast (bk.length a) j) = Sum.inr h.val ∧
        key h = (bk.word.toEmbedding.trans key) w := by
  constructor
  · intro h
    exact ⟨bk.word w,(bk.hit a j w).mp h,rfl⟩
  · rintro ⟨h,read,eqn⟩
    have same : h = bk.word w := key.injective eqn
    exact (bk.hit a j w).mpr (same ▸ read)

section
variable {F P I J V : Type} [Field F] [Fintype I] [DecidableEq V]
  {d p R Z : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {B : BitDescription W}
  (s : WorldShape p R B) (hp : 0<p) (one : 1≤R) (pins : ∀ a,p∣bits a)
  (G : PoweredGadget F) (pick : I×Fin 2 ↪ W.graph.Edge) (z : I→ℕ)
  (pos : ∀j,0<z j) (fit : ∀j a,W.graph.width (pick (j,a))=z j*G.b)
  (room : ∀j,z j≤Z) (pack : W.graph.Site→J) (profile : I→Profile G.C) (units : ∀j,p∣z j)
local notation "M" => GadgetNetwork.physical W.graph pick (branchWidth G z profile)
local notation "A" => W.selected G pick z pos fit pack profile
local notation "gmap" => GadgetNetwork.newSite W.graph pick (bestLayout (branchWidth G z profile)) pack
local notation "priorShape" => s.selected hp one pins G pick z pos fit room pack profile units
local instance privateBasisCoalescedSites : Fintype (Merged W.graph pick (bestLayout (branchWidth G z profile)) pack) := mergedFinite W.graph pick (bestLayout (branchWidth G z profile)) pack
local notation "zeroSite" => fun _ : (A).graph.Site => (0 : EuclideanSpace ℝ (Fin d))
local notation "zeroBound" => fun v : (A).graph.Site => (by simp : ‖zeroSite v‖≤1)
local notation "phys" => physicalBits G W.toWorld pick z room profile B.recipe
local notation "physShape" => physicalShape W B G pick z room profile hp s.sites s.edges pins units
local notation "divides" => physical_multiple W G pick z profile s.edges units
local notation "qnet" => quotient M gmap zeroSite zeroBound
local notation "qbits" => quotientBits M gmap zeroSite zeroBound phys
local notation "qshape" => quotientShape M gmap zeroSite zeroBound phys physShape divides
variable (key : (W.selected G pick z pos fit pack profile).graph.Site → DescentHostDirectory.Key V) (hub : V → Bool) (k g : ℕ)
local notation "addr" => MarkedWorld.address A key hub k g
local notation "H" => ↥(MarkedWorld.reclaimed A key hub k g)
local notation "zeroHome" => fun _ : H => (0 : EuclideanSpace ℝ (Fin d))
local notation "homeBound" => fun v : H => (by simp : ‖zeroHome v‖≤1)

/-- Read a coalesced private word in the two physical quotients that formed it. -/
def coalescedBookWord (h : H) :
    ((((priorShape).coalesced key hub k g).sites h).recipe hp).UsedWord ↪
      ((quotientShape qnet addr zeroHome homeBound qbits qshape (fun e=>divides e.val) h).recipe hp).UsedWord :=
  Function.Embedding.refl _

end

variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "prior" => sh.selected hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
local notation "cut" => (ticket.quantum.symm ▸ ticket.cuts)
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "common" => ticket.issued.common_chart he T c ((r).state c)
local notation "found" => (Classical.choose_spec common).2 hp prior unit cut
def privateChart := Function.const _ (activeChart ticket) found
local notation "b" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ))
local notation "pre" => (prior).coalesced ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
def privateBooks : SiteBooks hp after pre := Classical.choose found
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
section
local instance privateBasisScannedSites : Fintype (DescentSixParty.Merged W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack) := mergedFinite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun x : (sel).graph.Site=> (by simp : ‖x₁ x‖≤1)
local notation "ok₂" => fun x : C=> (by simp : ‖x₂ x‖≤1)
local notation "halo" => chartHalo (cap:=cap) (c:=c) b
local notation "reaches" => chartHalo_members ticket b
local notation "old" => cap.order.trans Fin.valEmbedding
variable {K : ℕ} (slot : ∀v,DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp)↪Fin K)
local notation "Peer" => ∀h : C, DescentPrivateRawLabels.LocalWire (p:=p) (r).pick uni prof loc h → ℕ
local notation "rawCode" => DescentPrivateRawLabels.privateKey (W:=W) (G:=G) (p:=p) (K:=K)
  (T:=(sel).graph.Site) («C»:=C) (I:=(r).pairs) (Z:=T.z) (b₁:=d) (b₂:=d) cap.placement old S cap.valid arch.bit
  (r).pick uni pos (r).fit room prof hp sh.sites sh.edges pin whole group addr x₁ x₂ ok₁ ok₂
  halo (reaches).1 (reaches).2.1 slot

private def physicalKey (h : C) (f : DescentPrivateRawLabels.LocalWire (p:=p) (r).pick uni prof loc h → ℕ) :=
  rawCode h f

/-- A pre-normalization site's private word in the physical double quotient. -/
def physicalBookWord (h : C) :=
  coalescedBookWord sh hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) h

/-- The physical key of a private word at a pre-normalization book site. -/
def bookWordKey (h : C) (f : DescentPrivateRawLabels.LocalWire (p:=p) (r).pick uni prof loc h → ℕ) :=
  (physicalBookWord ticket arch hp one pin sh unit h).trans
    (physicalKey ticket arch hp one pin sh unit slot h f)

local notation "code" => bookWordKey ticket arch hp one pin sh unit slot

section
attribute [local irreducible] BitDescription.scannedRows privateChart privateBooks physicalBookWord physicalKey bookWordKey

def reachedPrivateKey (peer : Peer) (v : n.result.graph.Site) : (((after).sites v).recipe hp).UsedWord ↪ Key :=
  ((bk).atSite v).word.toEmbedding.trans (code ((bk).home v) (peer ((bk).home v)))

/-- The same ordinal within the same active operand list reads the same compact key.
A physical cut or state renaming never silently changes a captured word to a public input. -/
theorem reachedPrivateRead (peer : Peer) (v : n.result.graph.Site) (a : (((after).sites v).recipe hp).Node)
    (j : Fin ((((after).sites v).recipe hp).arity a)) (w : (((after).sites v).recipe hp).UsedWord) :
    let a':=((bk).atSite v).node a
    let j':=Fin.cast (((bk).atSite v).length a) j
    ((((after).sites v).recipe hp).operand a j=Sum.inr w.val) ↔
      ∃h : (((pre).sites ((bk).home v)).recipe hp).UsedWord,
        (((pre).sites ((bk).home v)).recipe hp).operand a' j'=Sum.inr h.val ∧
        code ((bk).home v) (peer ((bk).home v)) h=reachedPrivateKey ticket arch hp one pin sh unit slot peer v w :=
  wordBook_read_key ((bk).atSite v) (code ((bk).home v) (peer ((bk).home v))) a j w

end
end

/-- The transported private word and the current public register refer to the same
unflattened node of the selected graph, even when several nodes read equal words. -/
theorem private_node (x : NodeOrder.All ((ticket.advance arch).bit)) :
    NodeOrder.coalescedNames _ ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
        ((bk).nodeAt hp x)=
      NodeOrder.castNames ((r).state c).symm _
        (NodeOrder.followNames n _ x) := (Classical.choose_spec found).2 x

theorem private_roots (x : NodeOrder.All ((ticket.advance arch).bit)) :
    NodeOrder.selectedNames arch.bit G (r).pick uni pos (r).fit room (r).pack prof
      (NodeOrder.coalescedNames _ ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) ((bk).nodeAt hp x))=
      roots ticket arch x :=congrArg _ (private_node ticket arch hp one pin sh unit x)

theorem private_site (x : (rawGraph he T c).Site) :
    (bk).home (n.destination (rawInput he T c ((r).state c) x))=loc x :=
  (Classical.choose_spec found).1 x

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
