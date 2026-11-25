import OAI.Hierarchy.DescentResetIssuedStencil
import OAI.Hierarchy.DescentFallbackCellLeaf

namespace OAI
/-! # The honest low stencil issues the same signed terminal fields as the selected reset -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le m g)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "H" => Host J V k
local notation "src" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "shortT" => fun t=>shortName c (T.code t)

open DescentPlainTerminal DescentPlainTerminal.Suffix
local notation "degreeAt" => fun u=>Z.placement.b (frame.host u)
local notation "limit" => fun u=>Nat.le_trans (Z.placement.depth (frame.host u)) (Nat.le_of_eq frame.extent)
local notation "sourceIx" => StarKeys.filled W.graph A.pos A.block digits
local notation "physicalSite" => home A
local notation "yAt" => fun u=>rearrange frame.basis (sourceIx u)
local notation "upperAt" => fun u=>high fits (yAt u)
local notation "lowerAt" => fun u=>@DescentPlainTerminal.low m T.commonDepth (yAt u)

private theorem transport_basis {m n : ℕ} (equal : m=n) (L : Layout n) (L' : Layout m) (same : HEq L L')
    (d : ℕ) (x : Block n) : group d (rearrange L' (Fin.cast (congrArg (fun i=>2^i) equal.symm) x))=
      group d (rearrange L x) := by
  subst m
  cases eq_of_heq same
  rfl

theorem issued_base_mode (u : W.graph.Site) :
    exceptionalCell A S ready digits Z T frame (physicalSite u)=
      (A.hub (A.pos u).2 || decide ((frame.host (A.pos u).2,group (degreeAt (A.pos u).2) (yAt u))∈Z.placement.keys)) := by
  let v:=(A.pos u).2
  have id:=transport_basis frame.extent frame.basis Z.placement.L frame.used (degreeAt v) (sourceIx u)
  have same : ((baseOf Z.placement.b Z.placement.depth Z.placement.L
       (frame.host v,Fin.cast (congrArg (fun j=>2^j) frame.extent.symm) (sourceIx u))).2).val=
         group (degreeAt v) (yAt u) := (layout_id _ _ _).trans id
  change decide ((baseOf _ _ _ (frame.host v,Fin.cast _ (sourceIx u)))∈validBases _ _ ∨ Z.placement.hub (frame.host v))=_
  have member : baseOf Z.placement.b Z.placement.depth Z.placement.L
      (frame.host v,Fin.cast (congrArg (fun j=>2^j) frame.extent.symm) (sourceIx u)) ∈
      validBases Z.placement.b Z.placement.keys ↔ (frame.host v,group (degreeAt v) (yAt u))∈Z.placement.keys := by
    rw [validBases,Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,label,same]
    rfl
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,Bool.or_eq_true]
  exact (member.or (frame.rotorHub v)).trans or_comm

theorem issued_fallback_word {n q₀ : ℕ} (vertex : V↪ℕ) (near : V→Finset V) (Y f B wire K Δ cap : ℕ)
    (wt : V→Block m→ℕ) (traffic : V→V→Block m→ℕ)
    (roster : ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame vertex near Y f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (inc : V→List V) (incoming : ∀u z,u∈inc z ↔ z∈near u)
    (ports : V→Fin q₀→Option (Contacts near)) (covered : ∀v e,Suffix.incident near v e ↔ ∃p,ports v p=some e)
    (trafficBound : ∀u v j,traffic u v j≤cap) (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (a : V→Block c→Stencil.panel (m-c) q₀ n)
    (words : ∀v hi,Stencil.Input fits near degreeAt frame.basis wt traffic A.hub Δ f B K g cap hi v (ports v) inc (a v hi))
    (s : Bool) (e : E) :
    let u:=src s e
    let cell:=physicalSite u
    Stencil.word (a (A.pos u).2 (upperAt u)) f B (2^Z.n) (lowerAt u)=2*DescentFallbackShapeTable.cell (m-c)
      (shortName c (T.code (fallbackCell A S ready digits Z T frame s cell))).2+
      (exceptionalCell A S ready digits Z T frame cell).toNat := by
  intro u cell
  let v:=(A.pos u).2
  let jx:=sourceIx u
  let hi:=upperAt u
  let lo:=lowerAt u
  let keys:=resetKeys near Δ f B K wt (fun u z i=>(traffic u z i:ℝ)) degreeAt limit frame.basis
  have keyeq (v:V) (z:ℕ) : (frame.host v,z)∈Z.placement.keys ↔ (v,z)∈keys:=roster.2.2.2.1 v z
  have samePred : (fun v z=>(frame.host v,z)∈Z.placement.keys)=(fun v z=>(v,z)∈keys) :=
    funext fun v=>funext fun z=>propext (keyeq v z)
  obtain ⟨safe,endpointAt,_⟩:=roster.2.2.2.2.2
  have trueRow:=endpointAt u
  rw [samePred] at trueRow
  have native:=Stencil.issued_word fits near degreeAt frame.basis wt traffic A.hub Δ f B K g (2^Z.n) cap
    hi v (ports v) inc (a v hi) (fun v=>T.commonLow _) frame.enough limit safe trafficBound hK hB hD
    incoming (covered v) (words v hi) lo
  dsimp only at native
  have center : join fits hi lo=yAt u:=join_high_low ..
  rw [center,Equiv.symm_apply_apply] at native
  rw [←trueRow] at native
  have placed:=issued_base_mode A S ready digits Z T frame u
  have keyRead (v:V) (z:ℕ) : decide ((frame.host v,z)∈Z.placement.keys)=decide ((v,z)∈keys) :=
    Bool.decide_congr (keyeq v z)
  rw [keyRead] at placed
  rw [cell_home A S ready digits Z T frame s e,←Stencil.shapeCode_fields,
    fields_relative,placed]
  exact native

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
