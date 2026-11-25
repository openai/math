import OAI.Hierarchy.DescentIssuedNodeOrder

namespace OAI
/-! # The two quotients and genuine actor venue of a selected stage -/

namespace Hierarchy.DescentSixParty.Normalize
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

/-- Follow one original site through every quotient and physical renaming. -/
def destination {W : MarkedWorld F d P bits} (n : Normalize W) : W.graph.Site → n.result.graph.Site := by
  induction n with
  | done W => exact id
  | split W q m fit rest ih => exact ih
  | merge W V key hub k g rest ih => exact fun x => ih (MarkedWorld.address W key hub k g x)
  | named W s e rest ih => exact fun x => ih (s x)

theorem destination_appendNames (n : Normalize W) (s : Equiv.Perm n.result.graph.Site)
    (e : Equiv.Perm n.result.graph.Edge) (x y : W.graph.Site) :
    (n.appendNames s e).destination x=(n.appendNames s e).destination y ↔ n.destination x=n.destination y := by
  induction n with
  | done W =>
    change s x = s y ↔ x = y
    exact s.injective.eq_iff
  | split _ _ _ _ rest ih=>exact ih s e x y
  | merge W V key hub k g rest ih=>exact ih s e _ _
  | named _ a _ rest ih=>exact ih s e (a x) (a y)
end
end Hierarchy.DescentSixParty.Normalize

namespace Hierarchy.DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentHostDirectory DescentNetworkPartition
open DescentHistoryOrder GadgetNetwork DescentPacking DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (BitDescription.ScanRows.pairs r)=>T.z) ((BitDescription.ScanRows.profile r) c)
abbrev rawGraph := physical W.graph (BitDescription.ScanRows.pick r) sw
abbrev scanWorld := W.selected G (BitDescription.ScanRows.pick r) (fun _=>T.z) (fun _=>T.unitPos) (BitDescription.ScanRows.fit r) (BitDescription.ScanRows.pack r) ((BitDescription.ScanRows.profile r) c)

/-- The first quotient carries the literal physical endpoint to the normalization's starting world. -/
def rawInput {A : MarkedWorld F d P bits} (input : A=scanWorld he T c) : (rawGraph he T c).Site→A.graph.Site :=
  fun x=>cast (congrArg (fun B : MarkedWorld F d P bits=>B.graph.Site) input.symm)
    (newSite W.graph (BitDescription.ScanRows.pick r) (bestLayout sw) (BitDescription.ScanRows.pack r) x)

local notation "layout" => bestLayout sw
/-- The witness retains the exact selected colony coordinates, old-site flags
and the native venue-key construction used when the stage was issued. -/
structure IssuedDonorChart (H : Type) [Fintype H] [DecidableEq H] where
  col : ScanColonies he T↪H×(ℕ×ℕ)
  same : ∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e)
  hub : H→Bool
  native : HEq col (nativeAddress he T)
  code : ∀ci,(col ci).2=(nativeAddress he T ci).2
  old : ∀v,HEq (col (scanHomeAt he T v)).1 (T.pos v) ∧ hub (col (scanHomeAt he T v)).1=T.hub v

def IssuedDonorChart.key (b : IssuedDonorChart he T H) : (scanWorld he T c).graph.Site↪Key H :=
  nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap b.col b.same layout

/-- Even a thin slot redirected to its chosen thick center uses a genuinely
occupied old-colony host. -/
theorem IssuedDonorChart.key_host (b : IssuedDonorChart he T H) (x : (scanWorld he T c).graph.Site) :
    ∃u,(b.key he T c x).1=(b.col (scanHomeAt he T u)).1 := by
  have address (p : ScanColonies he T⊕StarKeys.NativeSlot W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap) :
      ∃ci,(StarKeys.packAddress W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap b.col p).1=(b.col ci).1 := by
    rcases p with ci|⟨ci,j⟩ <;> exact ⟨ci,rfl⟩
  have located : ∃ci,(b.key he T c x).1=(b.col ci).1 := address _
  obtain ⟨ci,here⟩:=located
  obtain ⟨u,rfl⟩:=scanHomeAt_surjective he T ci
  exact ⟨u,here⟩

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
