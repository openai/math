import OAI.Hierarchy.DescentExteriorSnapshotFields
import OAI.Hierarchy.DescentOrdinaryPublicDegree
import OAI.Hierarchy.DescentFixedResetHops
import OAI.Hierarchy.DescentChronologicalGrains

namespace OAI
/-! # A common public literal image for ordinary and reset dates -/

namespace Hierarchy.DescentSixParty.Chronology
open Catalyst Computability.BorderVNP.Crossing DescentCompiler DescentHostDegree DescentKernelHistory DescentColonies
open DescentExteriorReplay DescentRotor ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k hwire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ i z D : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ hwire hist}
  {current : Reached W G q ε S k i z D hwire hist}
  {D' n' h' C' f' g' cut' tail' : ℕ}

private def atDate {α : Type} (l : List α) (t : ℕ) (blank : α) := ((l.drop t).head?).getD blank

private theorem at_append {α : Type} (xs ys : List α) (v fallback : α) (t : ℕ) (len : xs.length=t) :
    atDate (xs++v::ys) t fallback=v := by
  rw [←len,atDate,List.drop_left]
  rfl

def SnapshotCalendar (ctl : ResetRates G S k D' n' h' C' f' g' cut' tail')
    (kinds : List Bool) (factors : List ℕ) (ranks : ℕ→Bank) : Snapshots k :=
  let ht:=GroupStage.depthBound D' n' f' g'
  let degree (t : ℕ):=OrdinaryLink.publicDegree S.rounds G.b (atDate factors t 0)
  let reset (t : ℕ):=atDate kinds t false
  {hosts:=S.hostSize,
   pitch:=fun t => if reset t then HopTables.resetPitch ctl.board k ht else HopTables.ordinaryPitch k (degree t),
   shape:=fun t => if reset t then HopTables.resetShape ctl.board k ht k g' else HopTables.ordinaryShape k (degree t),
   compact:=fun t => if reset t then some (ranks t) else none}

omit [Fintype P] in
/-- Both static-geometry projections use the same issued epoch that supplied
the reset rotor and cap calendar. Earlier shape pages are literal constants. -/
theorem Path.labels_from_calendar (path : Path initial current)
    (ctl : ResetRates G S k D' n' h' C' f' g' cut' tail')
    (kinds : List Bool) (factors : List ℕ) (ranks : ℕ→Bank)
    (ks : ∃tail,path.kinds++tail=kinds) (fs : ∃tail,path.capFactors++tail=factors)
    (rotor : path.OnlyRotor (RotorSpec.ofRates ctl)) :
    path.snapshotLabels (SnapshotCalendar ctl kinds factors ranks) := by
  induction path with
  | here => trivial
  | @ordinary _ age _ Di _ _ src prev _ _ _ _ _ _ ticket ih =>
    rcases ks with ⟨kt,hk⟩
    rcases fs with ⟨ft,hf⟩
    change (prev.kinds++[false])++kt=kinds at hk
    change (prev.capFactors++[ticket.factor])++ft=factors at hf
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hk hf
    have lk : prev.kinds.length=age := by simpa using prev.kinds_length
    have lf : prev.capFactors.length=age := by simpa using prev.capFactors_length
    have kind : atDate kinds age false=false := hk ▸ at_append _ _ _ _ _ lk
    have val : atDate factors age 0=ticket.factor := hf ▸ at_append _ _ _ _ _ lf
    have degree : OrdinaryLink.publicDegree S.rounds G.b ticket.factor=Di :=
      ticket.public_degree.trans src.branch
    refine ⟨ih ⟨_,hk⟩ ⟨_,hf⟩ rotor,?_,?_⟩ <;>
      simp only [SnapshotCalendar,kind,val,degree,Bool.false_eq_true,↓reduceIte]
  | @reset _ age _ Di n h C f g cut tail src prev ctl₀ b ih =>
    rcases ks with ⟨kt,hk⟩
    rcases fs with ⟨ft,hf⟩
    change (prev.kinds++[true])++kt=kinds at hk
    change (prev.capFactors++[b.factor])++ft=factors at hf
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hk hf
    have lk : prev.kinds.length=age := by simpa using prev.kinds_length
    have kind : atDate kinds age false=true := hk ▸ at_append _ _ _ _ _ lk
    obtain ⟨past,board⟩:=rotor
    obtain ⟨oldPitch,oldShape⟩:=HopTables.reset_public b
    obtain ⟨newPitch,newShape⟩:=HopTables.reset_hop_geometry b ctl board
    exact ⟨ih ⟨_,hk⟩ ⟨_,hf⟩ past,
      by simpa only [SnapshotCalendar,kind,↓reduceIte] using newPitch.symm.trans oldPitch,
      by simpa only [SnapshotCalendar,kind,↓reduceIte] using newShape.symm.trans oldShape⟩

omit [Fintype P] in
theorem Path.issued_snapshot_labels (path : Path initial current)
    (ctl : ResetRates G S k D' n' h' C' f' g' cut' tail') (ranks : ℕ→Bank)
    (kinds : path.kinds=kindCalendar S.rounds S.height)
    (factors : path.capFactors=capCalendar G.b S.rounds g' S.height)
    (rotor : path.OnlyRotor (RotorSpec.ofRates ctl)) :
    path.snapshotLabels (SnapshotCalendar ctl (kindCalendar S.rounds S.height)
      (capCalendar G.b S.rounds g' S.height) ranks) :=
  path.labels_from_calendar ctl _ _ ranks ⟨[],by simpa using kinds⟩ ⟨[],by simpa using factors⟩ rotor

end
end Hierarchy.DescentSixParty.Chronology

end OAI
