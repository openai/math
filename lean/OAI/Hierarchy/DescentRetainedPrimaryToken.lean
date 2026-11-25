import OAI.Hierarchy.DescentRetainedHomePrefix
import OAI.Hierarchy.DescentRetainedPrimitiveOrigin
import OAI.Hierarchy.DescentRetainedPacketMask

namespace OAI
/-! # The real preceding primitive of an inherited node at the physical primary -/
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1400000 in
include roster stencil in
/-- The slot numbers are the actual old and new chronological node numbers. The
old amount is the preceding archive's population at the measured former coordinate. -/
theorem primary_token (seen : DescentRetainedControl.filter (D:=mover.degree) (L:=(v).donors) (cap:=mover.cap)
      (which shape) (window carrier coarse)=vector takeDonor sorted)
    {N : ℕ} (oldId : A.graph.Site↪Fin N) (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (Node : A.graph.Site→Type) [∀u,Fintype (Node u)] (priorNode : ∀u,Node u≃Fin (Fintype.card (Node u)))
    (previous : ∀lo,(v).originalCount wrd (coords.symm lo)=∑u : A.graph.Site,
      if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (z : Node pivot.val) (j : Fin mover.transfer.previousNodes)
    (former : j.val=(priorNode pivot.val z).val) (nxt : Fin mover.transfer.nodes)
    (named : nxt.val=(DescentResetLocalNodes.oldOrder (fun u : DescentNamedContact.Fibre T.home t=>Node u.val)
      ((Z.homeTicket T oldId t).trans Fin.valEmbedding)
      (fun u=>(priorNode u.val).toEmbedding.trans Fin.valEmbedding) ⟨pivot,z⟩).val) :
    let d:=coords.symm (low («c»:=c) (μ (ix pivot.val)))
    mover.targetInputs which window strips (finProdFinEquiv (nxt,shape)) carrier coarse=(v).entry wrd d j (v).occupiedField:=by
  intro d
  let order:=physicalDonorOrder frame t v coords
  have comparison (i k : Fin mover.transfer.donors) : sorted i k=decide ((order i).val<(order k).val):=by
    simp only [order,←Fin.lt_def,physicalDonorOrder_lt frame t v coords]
  have home:=old_home_register (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil pivot
  have yes : takeDonor d=true:=by simp [d,home]
  have serial:=primary_node_number (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil v coords wrd
    oldId ordered Node priorNode previous pivot z
  have src:=frame.homeHost pivot.val
  rw [pivot.property] at src
  have hh : pos pivot.val=v₀:=(Equiv.eq_symm_apply _).mpr src.symm
  have original:=old_home_digit (A:=A) (Z:=Z) (T:=T) frame t pivot
  have card : Fintype.card (Node pivot.val)≤(v).originalCount wrd d:=by
    rw [show d=coords.symm (low («c»:=c) (μ (ix pivot.val))) from rfl,previous]
    have term:=Finset.single_le_sum (f:=fun u : A.graph.Site=>if pos u=v₀ ∧ ix u=raw (low («c»:=c) (μ (ix pivot.val)))
      then Fintype.card (Node u) else 0) (fun _ _=>Nat.zero_le _) (Finset.mem_univ pivot.val)
    simpa only [ite_eq_left (And.intro hh original)] using term
  apply mover.chosen_donor which window strips shape nxt carrier coarse takeDonor sorted order seen comparison d j yes
  · rw [former]
    exact named.trans serial
  · rw [former]
    exact (priorNode pivot.val z).isLt.trans_le card

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
