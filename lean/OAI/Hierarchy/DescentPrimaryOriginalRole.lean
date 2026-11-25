import OAI.Hierarchy.DescentRetainedPrimaryToken
import OAI.Hierarchy.DescentRetainedPrimitivePadding
import OAI.Hierarchy.DescentRetainedRoleOccupancy

namespace OAI
/-! # Previous primitive at the selected low digit, also when the real primary runs out -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentSixParty.ResetInput DescentContacts DescentColonies DescentGL
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel DescentChosenRouter
open DescentRelativeContacts DescentResetHostSize DescentFallbackShapeTable
open DescentHostDirectory DescentPackedActorMask DescentSIMDLookup
open DescentRetainedControl DescentRetainedHomeMover
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
    {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
    (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ) (wt : V→Block k→ℕ)
    (flow : V→V→Block k→ℝ) (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "c" => T.commonDepth
local notation "Y" => (2^Z.n:ℕ)
local notation "r" => Z.k-c
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
set_option quotPrecheck false in
local notation "safe" => roster.2.2.2.2.2.choose
local notation "ep" => endpoint near (fun (v : V)=>Z.placement.b (frame.host v)) frame.basis wt f
  (32*Nat.clog 2 (2*Δ)) B g Y safe (fun (v : V) (j : ℕ)=>(frame.host v,j)∈Z.placement.keys) hub
local notation "μ" => rearrange frame.basis
variable (t : Z.Fallback)
set_option quotPrecheck false in
local notation "v₀" => frame.host.symm (T.code t).1
set_option quotPrecheck false in
local notation "hi" => Z.rootBlock T (.inr t)
set_option quotPrecheck false in
local notation:max "name" t:arg => (shortName c (T.code t)).2
local notation:max "code" t:arg => cell r (name t)
set_option quotPrecheck false in
local notation:max "raw" j:arg => (μ).symm (join fit hi j)
variable (word : Block (k-T.commonDepth)→ℕ)


variable (stencil : ∀ lo : Block (k-T.commonDepth), word lo/2 =
    Stencil.shapeCode (k-T.commonDepth) (2^Z.n) (fieldsRelative T.commonDepth
      (endpoint near (fun (u : V) => Z.placement.b (frame.host u)) frame.basis wt f
        (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) roster.2.2.2.2.2.choose
        (fun (u : V) (j : ℕ) => (frame.host u,j) ∈ Z.placement.keys) hub (frame.host.symm (T.code t).1)
        ((rearrange frame.basis).symm (join (frame.enough.trans (Nat.sub_le ..)) (Z.rootBlock T (.inr t)) (lo))))))


variable (mover : DescentRetainedHomeMover.Layout)
local notation "v" => mover.transfer
variable (coords : Fin mover.transfer.donors≃Block (k-T.commonDepth)) (shape : Fin mover.shapes) (carrier : Fin mover.transfer.hosts) (coarse : Fin mover.transfer.grouped)
    (which : Fin mover.shapes→Option ℕ) (window : Fin mover.transfer.hosts→Fin mover.transfer.grouped→Cell mover.control.rootWidth)
    (strips : Fin mover.transfer.channels→Fin mover.transfer.hosts→Fin mover.transfer.grouped→Cell mover.transfer.stripWord)
local notation "wrd" => (v).site strips carrier coarse
local notation "takeDonor" => fun i : Fin mover.transfer.donors=>decide (word (coords i)/2=code t)
local notation "sorted" => fun i j : Fin mover.transfer.donors=>decide (raw (coords i)<raw (coords j))

open DescentOrdinaryAtomFieldRAM DescentSixParty.PackedFlow.Channels
variable (seen : DescentRetainedControl.filter (D:=mover.degree) (L:=mover.transfer.donors) (cap:=mover.cap)
    (which shape) (window carrier coarse) = vector
      (fun j : Fin mover.transfer.donors => decide (word (coords j)/2 = cell (Z.k-T.commonDepth) (shortName T.commonDepth (T.code t)).2))
      (fun a b : Fin mover.transfer.donors => decide ((rearrange frame.basis).symm (join (frame.enough.trans (Nat.sub_le ..)) (Z.rootBlock T (.inr t)) (coords a)) < (rearrange frame.basis).symm (join (frame.enough.trans (Nat.sub_le ..)) (Z.rootBlock T (.inr t)) (coords b)))))

set_option maxHeartbeats 1200000 in
include roster stencil seen in
theorem primary_no_node (amount:A.graph.Site→ℕ) (previous:∀lo,
    (v).originalCount wrd (coords.symm lo)=∑u : A.graph.Site,if pos u=v₀ ∧ ix u=raw lo then amount u else 0)
    (nxt:Fin (v).nodes) (absent:(∑u:DescentNamedContact.Fibre T.home t,amount u.val)≤nxt.val) :
    mover.targetInputs which window strips (finProdFinEquiv (nxt,shape)) carrier coarse=0:=by
  let order:=physicalDonorOrder frame t v coords
  have comparison (i j : Fin mover.transfer.donors) : sorted i j=decide ((order i).val<(order j).val):=by
    simp only [order,←Fin.lt_def,physicalDonorOrder_lt frame t v coords]
  apply mover.ghost which window strips shape nxt carrier coarse takeDonor sorted order seen comparison
  apply le_trans _ absent
  have together:=window_sum (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil id amount
    (fun lo=>(v).originalCount wrd (coords.symm lo)) previous
  apply Eq.le
  calc
    _ = ∑ j, (fun lo : Block (k-c) => if word lo/2=code t then (v).originalCount wrd (coords.symm lo) else 0) (coords j) := by
      simp only [decide_eq_true_eq, Equiv.symm_apply_apply]
    _ = _ := (coords.sum_comp _).trans together

variable (size : 2^(mover.transfer.high+mover.transfer.low)=mover.transfer.groups*mover.transfer.blocks) (cut : mover.transfer.cut ≤ mover.transfer.high+mover.transfer.low)
    (L : DescentGL.Layout (mover.transfer.high+mover.transfer.low)) (X : Fin mover.transfer.blocks→Fin mover.transfer.hosts→Fin mover.transfer.groups→Cell mover.transfer.wholeWord)
local notation "sources" => mover.oldStrips size cut L X
local notation "packed" => (v).site sources carrier coarse
local notation:max "rail" lo:arg => (rearrange L).symm (DescentIssuedFallbackPanel.join cut coarse (coords.symm lo))
local notation:max "oldPos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)) : Fin mover.transfer.groups×Fin mover.transfer.blocks)
variable (Node : A.graph.Site→Type) [∀u,Fintype (Node u)]
local notation:max "census" lo:arg => ∑u : A.graph.Site,if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0

omit [Fintype V] in
/-- Input words are the actual previous primitive page at the inverse-GL donor.
A predecessor seed or reset with external nodes uses all its nonzero tokens. -/
theorem old_token_census (lo : Block (k-c)) (bound : census lo≤(v).previousNodes)
    (loaded : ∀j:Fin (v).previousNodes,(ScalarOperand.take (a:=(v).bits) j (X (oldPos lo).2 carrier (oldPos lo).1)).val≠0 ↔ j.val<census lo) :
    (v).originalCount packed (coords.symm lo)=census lo:=
  mover.previous_count size cut L X carrier coarse (coords.symm lo) _ bound loaded

set_option maxHeartbeats 1200000 in
include roster stencil seen in
theorem moved_old_original {N : ℕ} (oldId:A.graph.Site↪Fin N)
    (ordered:∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (priorNode:∀u,Node u≃Fin (Fintype.card (Node u))) (bound:∀lo,census lo≤(v).previousNodes)
    (loaded:∀lo (j:Fin (v).previousNodes),(ScalarOperand.take (a:=(v).bits) j (X (oldPos lo).2 carrier (oldPos lo).1)).val≠0 ↔ j.val<census lo)
    (pivot:DescentNamedContact.Fibre T.home t) (atom:Node pivot.val) (j:Fin (v).previousNodes)
    (former:j.val=(priorNode pivot.val atom).val) (nxt:Fin (v).nodes)
    (named:nxt.val=(DescentResetLocalNodes.oldOrder (fun u:DescentNamedContact.Fibre T.home t=>Node u.val)
      ((Z.homeTicket T oldId t).trans Fin.valEmbedding)
      (fun u=>(priorNode u.val).toEmbedding.trans Fin.valEmbedding) ⟨pivot,atom⟩).val) :
    let lo:=low («c»:=c) (μ (ix pivot.val))
    mover.targetInputs which window sources (finProdFinEquiv (nxt,shape)) carrier coarse=
      ScalarOperand.take (a:=(v).bits) j (X (oldPos lo).2 carrier (oldPos lo).1):=by
  intro lo
  have prev (a : Block (k-c)):=old_token_census (A:=A) (Z:=Z) (T:=T) frame t mover coords carrier coarse size cut L X Node a (bound a) (loaded a)
  rw [primary_token (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil mover coords shape
    carrier coarse which window sources seen oldId ordered Node priorNode prev pivot atom j former nxt named]
  change (v).entry packed (coords.symm lo) j (v).occupiedField = _
  have cell := (v).prior_digit (mover.toLayout.priorValues X) size cut L carrier coarse (coords.symm lo) j (v).occupiedField
  simp only [DescentRetainedPrimitive.Layout.priorValues, DescentResetRetainedSetup.Layout.sourceID, Equiv.symm_apply_apply] at cell
  exact cell

set_option maxHeartbeats 1200000 in
include roster stencil seen in
theorem moved_old_padding (bound:∀lo,census lo≤(v).previousNodes)
    (loaded:∀lo (j:Fin (v).previousNodes),(ScalarOperand.take (a:=(v).bits) j (X (oldPos lo).2 carrier (oldPos lo).1)).val≠0 ↔ j.val<census lo)
    (nxt:Fin (v).nodes) (empty:(∑u:DescentNamedContact.Fibre T.home t,Fintype.card (Node u.val))≤nxt.val):
    mover.targetInputs which window sources (finProdFinEquiv (nxt,shape)) carrier coarse=0:=
  primary_no_node (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil mover coords shape carrier coarse which window sources
    seen (fun u=>Fintype.card (Node u))
    (fun lo=>old_token_census (A:=A) (Z:=Z) (T:=T) frame t mover coords carrier coarse size cut L X Node lo (bound lo) (loaded lo)) nxt empty

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
