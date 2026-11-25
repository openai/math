import OAI.Hierarchy.DescentPrimaryOriginalRole
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
variable (previousHost : V) (highBlock : Block T.commonDepth) (shapeKey : ℕ) (word : Block (k-T.commonDepth)→ℕ)
local notation:max "code" t:arg => cell r (shortName c (T.code t)).2
local notation:max "raw" j:arg => (μ).symm (join fit highBlock j)
variable (stencil : ∀ lo : Block (k-T.commonDepth), word lo/2 =
    Stencil.shapeCode (k-T.commonDepth) (2^Z.n) (fieldsRelative T.commonDepth
      (endpoint near (fun (u : V) => Z.placement.b (frame.host u)) frame.basis wt f
        (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) roster.2.2.2.2.2.choose
        (fun (u : V) (j : ℕ) => (frame.host u,j) ∈ Z.placement.keys) hub previousHost
        ((rearrange frame.basis).symm (join (frame.enough.trans (Nat.sub_le ..)) highBlock (lo))))))
variable (empty : ¬∃t : Z.Fallback,(T.code t).1=frame.host previousHost ∧
  Z.rootBlock T (.inr t)=highBlock ∧ cell (Z.k-T.commonDepth) (shortName T.commonDepth (T.code t)).2=shapeKey)

set_option maxHeartbeats 1200000 in
include roster stencil empty in
/-- A raw shape can be a true primary for a *different* coarse group. If its
current geometry has no terminal, no matching previous primitive can be accepted. -/
theorem earlier_window_empty (amount : A.graph.Site→ℕ) (old : Block (k-T.commonDepth)→ℕ)
    (previous:∀lo,old lo=∑u : A.graph.Site,if pos u=previousHost ∧ ix u=raw lo then amount u else 0) :
    (∑lo:Block (k-c),if word lo/2=shapeKey then old lo else 0)=0:=by
  apply Finset.sum_eq_zero
  intro lo _
  by_cases yes:word lo/2=shapeKey
  · rw [ite_eq_left yes,previous]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hit:pos u=previousHost ∧ ix u=raw lo
    · have label:=roster.2.2.2.2.2.choose_spec.1 u
      rw [hit.1,hit.2] at label
      have data:word lo/2=code (T.home u):=by
        rw [stencil,←label,←fields_relative,←frame.extent,Stencil.shapeCode_fields]
      have host:(T.code (T.home u)).1=frame.host previousHost:=(frame.homeHost u).trans (congrArg _ hit.1)
      have high:Z.rootBlock T (.inr (T.home u))=highBlock:=by
        apply Fin.ext
        have loc:=frame.homeHigh u
        rw [hit.2,Equiv.apply_symm_apply] at loc
        exact loc.trans (congrArg Fin.val (high_join fit highBlock lo))
      exact (empty ⟨T.home u,host,high,data.symm.trans yes⟩).elim
    · simp [hit]
  · simp [yes]

variable (mover:DescentRetainedHomeMover.Layout)
local notation "v" => mover.transfer
variable (coords:Fin mover.transfer.donors≃Block (k-T.commonDepth)) (shape:Fin mover.shapes) (carrier:Fin mover.transfer.hosts) (coarse:Fin mover.transfer.grouped)
    (which:Fin mover.shapes→Option ℕ) (window:Fin mover.transfer.hosts→Fin mover.transfer.grouped→Cell mover.control.rootWidth)
    (strips:Fin mover.transfer.channels→Fin mover.transfer.hosts→Fin mover.transfer.grouped→Cell mover.transfer.stripWord)
local notation "takeDonor" => fun i:Fin mover.transfer.donors=>decide (word (coords i)/2=shapeKey)
local notation "before" => fun i j:Fin mover.transfer.donors=>decide (raw (coords i)<raw (coords j))
local notation "wrd" => (v).site strips carrier coarse

set_option maxHeartbeats 1200000 in
include roster stencil empty in
theorem vacancy_token (nxt:Fin mover.transfer.nodes) (amount : A.graph.Site→ℕ)
    (previous:∀lo,(v).originalCount wrd (coords.symm lo)=∑u:A.graph.Site,if pos u=previousHost ∧ ix u=raw lo then amount u else 0)
    (sensed : DescentRetainedControl.filter (D:=mover.degree) (L:=(v).donors) (cap:=mover.cap)
      (which shape) (window carrier coarse)=vector takeDonor before) :
    mover.targetInputs which window strips (finProdFinEquiv (nxt,shape)) carrier coarse=0:=by
  let rank : Fin mover.transfer.donors↪ℕ:=⟨fun i=>(raw (coords i)).val,by
    intro a b h
    have glued:=(μ).symm.injective (Fin.ext h)
    exact coords.injective (by simpa only [low_join] using congrArg (low («c»:=c)) glued)⟩
  let order:=(DescentPhysicalOrder.physical rank).trans (finCongr (Fintype.card_fin _))
  have cmp a b : before a b=decide ((order a).val<(order b).val):=by
    have hlt : order a < order b ↔ raw (coords a) < raw (coords b) :=
      DescentPhysicalOrder.physical_lt_iff rank a b
    exact Bool.decide_congr hlt.symm
  apply mover.ghost which window strips shape nxt carrier coarse takeDonor before order sensed cmp
  have zero:=earlier_window_empty (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster previousHost highBlock shapeKey word
    stencil empty amount (fun lo=>(v).originalCount wrd (coords.symm lo)) previous
  rw [←coords.sum_comp] at zero
  simpa only [decide_eq_true_eq,Equiv.symm_apply_apply] using zero.le.trans (Nat.zero_le nxt.val)

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
