import OAI.Hierarchy.DescentPackedMatchSourceSeat
import OAI.Hierarchy.DescentPackedMatchedGeometry

namespace OAI
/-! # Exactly one occupied source seat and genuinely zero unoccupied packed requests -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentColonies DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage

open DescentKernelHistory DescentGL DescentHostDegree in
theorem source_host (u : W.graph.Site) : (addr (home u)).1=A.pos u := by
  let T := A.stage
  let μ := (BitDescription.scannedRows he T).μ
  let blocks := BitDescription.scanBlocks T μ
  let units := W.siteUnits T.hub T.records T.wire 256 T.hist
  have fit := small_reindexed W.graph T.pos T.block units T.small (multiplier T.fieldBits μ)
  have decoded := occupiedAddress_colonyOf W.graph (T.wire*(T.z*G.b)*T.cap) T.near
    (gap T.Δ) (packExponent 20 T.Δ) (blockMass W.graph T.pos blocks units) fit T.pos blocks u
  exact congrArg (fun v : (J×V)×(ℕ×ℕ) => v.1) decoded

/-- `win` is the selected old-block column supplied by the native winner run.
A positive source key is present precisely when one of the original actors has that key. -/
theorem occupied_key (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (addr (home u)).2+(scanColorAt he A.stage u).toNat)
    (h : J×V) (key : ℕ) :
    (∃x,(panel h).winner x≠0 ∧ leaf ((panel h).winner x).val=key) ↔
      ∃c : ScanColonies he A.stage,(addr c).1=h ∧ heap (addr c).2=key := by
  have on (u : W.graph.Site) : ((panel (A.pos u)).winner (A.block u)).val=1+2*heap (addr (home u)).2+(scanColorAt he A.stage u).toNat :=
    (real_winner A native S ready names win next u (fit u)).trans (winner u)
  have leafAt (u : W.graph.Site) : leaf ((panel (A.pos u)).winner (A.block u)).val=heap (addr (home u)).2 := by
    rw [leaf,on u]
    cases scanColorAt he A.stage u <;> simp; omega
  constructor
  · rintro ⟨x,active,where_⟩
    by_cases here : ∃u,A.pos u=h ∧ A.block u=x
    · obtain ⟨u,rfl,rfl⟩ := here
      exact ⟨home u,source_host A he u,(leafAt u).symm.trans where_⟩
    · exact False.elim (active (empty_winner A native S ready names win next h x here))
  · rintro ⟨c,place,code⟩
    have covered : Function.Surjective home := scanHomeAt_surjective he A.stage
    obtain ⟨u,rfl⟩ := covered c
    rw [source_host A he u] at place
    subst h
    refine ⟨A.block u,?_,(leafAt u).trans code⟩
    intro no
    have contradiction := on u
    rw [no] at contradiction
    simp only [Fin.val_zero] at contradiction
    omega

theorem ghost_inputs (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (addr (home u)).2+(scanColorAt he A.stage u).toNat)
    (s : Shape) (B key : ℕ) (h : J×V) (empty : ¬∃c : ScanColonies he A.stage,(addr c).1=h ∧ heap (addr c).2=key) :
    inputs s B key (panel h) (fun _=>0)=⟨fun _=>0,fun _=>0,fun _ _=>0,fun _ _=>0,fun _=>0⟩ := by
  have absent := (occupied_key A native S ready names win next he fit winner h key).not.mpr empty
  exact vacant s B key (panel h) (fun x alive leaf_=>absent ⟨x,alive,leaf_⟩)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
