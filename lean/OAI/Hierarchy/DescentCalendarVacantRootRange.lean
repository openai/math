import OAI.Hierarchy.DescentVacantPrimaryToken
import OAI.Hierarchy.DescentDecodedEmptyPrimary

namespace OAI
/-! # Range words on an empty root of a physical primary -/
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

open DescentRetainedRangeDigits
variable (chart:DescentResetOperandSetup.Chart)
local notation "v" => chart.retained
variable (coords:Fin chart.retained.donors≃Block (k-T.commonDepth)) (shape:Fin chart.placement.shapes) (carrier:Fin chart.retained.hosts) (coarse:Fin chart.retained.grouped)
    (which:chart.seven.control.Targets) (window:chart.seven.Packets) (strips:chart.retained.Strips)
local notation "takeDonor" => fun i:Fin (v).donors=>decide (word (coords i)/2=shapeKey)
local notation "before" => fun i j:Fin (v).donors=>decide (raw (coords i)<raw (coords j))
local notation "wrd" => (v).site strips carrier coarse

include roster stencil empty in
theorem calendar_vacant_root_range (nxt:Fin (v).nodes) (arg:Fin (v).args) (f₀:Fin 3) (amount : A.graph.Site→ℕ)
    (previous:∀lo,(v).originalCount wrd (coords.symm lo)=∑u:A.graph.Site,if pos u=previousHost ∧ ix u=raw lo then amount u else 0)
    (own : ownerAt chart which window shape carrier coarse=takeDonor)
    (comparison : priorAt chart window carrier coarse=before) :
    chart.seven.decoded which window strips ((v).outputID 1 (page f₀) arg nxt) shape carrier coarse=0:=by
  let rank : Fin (v).donors↪ℕ:=⟨fun i=>(raw (coords i)).val,by
    intro a b h
    have glued:=(μ).symm.injective (Fin.ext h)
    exact coords.injective (by simpa only [low_join] using congrArg (low («c»:=c)) glued)⟩
  let order:=(DescentPhysicalOrder.physical rank).trans (finCongr (Fintype.card_fin _))
  have cmp a b : before a b=decide ((order a).val<(order b).val):=by
    have hlt : order a < order b ↔ raw (coords a) < raw (coords b) :=
      DescentPhysicalOrder.physical_lt_iff rank a b
    exact Bool.decide_congr hlt.symm
  have native a b : priorAt chart window carrier coarse a b=decide ((order a).val<(order b).val):=by
    rw [comparison];exact cmp a b
  apply decoded_empty chart which window strips shape carrier coarse order ((v).original_rank _ order native) nxt _ arg f₀
  rw [own]
  have zero:=earlier_window_empty (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster previousHost highBlock shapeKey word
    stencil empty amount (fun lo=>(v).originalCount wrd (coords.symm lo)) previous
  rw [←coords.sum_comp] at zero
  simpa only [decide_eq_true_eq,Equiv.symm_apply_apply] using zero.le.trans (Nat.zero_le nxt.val)

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
