import OAI.Hierarchy.DescentPublicStepKinds
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # The public bit quantum on every selected chronological ordinary step -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : AtomSchedule} {q ε : ℝ} {k w h₀ : ℕ}
variable {W₀ W₁ W₂ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ : ℕ}
variable {first : Reached W₀ G q ε S k i₀ z₀ D₀ w h₀}
    {middle : Reached W₁ G q ε S k i₁ z₁ D₁ w h₀}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ w h₀}

def Path.ClosedPeriod (path : Path first middle) : Prop :=
  match path with
  | .reset earlier _=>earlier.ordinaryOnly
  | _=>False

def OrdinaryLink.GrainDate {u : ℝ} {he : 0≤ε} {T : StageInput W₀ G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i₀+1) z₁ D₁ w h₀}
    (_ticket : OrdinaryLink first he T c n target) (p : ℕ) : Prop := T.z=S.grainAt G.b p i₀

def Path.GrainDates (p : ℕ) (path : Path first middle) : Prop := by
  induction path with
  | here => exact True
  | ordinary prev ticket ih => exact ih ∧ ticket.GrainDate p
  | reset prev closed ih => exact ih

theorem Path.grainDates_append (x : Path first middle) (y : Path middle last) (p : ℕ) :
    (x.append y).GrainDates p ↔ x.GrainDates p ∧ y.GrainDates p := by
  induction y with
  | here=>simp [append,GrainDates]
  | ordinary prev step ih =>
    change (GrainDates p (x.append prev) ∧ step.GrainDate p) ↔
      GrainDates p x ∧ (GrainDates p prev ∧ step.GrainDate p)
    rw [ih, and_assoc]
  | reset prev step ih=>exact ih

theorem OrdinaryLink.grain_on_cut {z' D' : ℕ} {u : ℝ}
    {he : 0≤ε} {T : StageInput W₁ G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i₁+1) z' D' w h₀}
    (ticket : OrdinaryLink middle he T c n target) (before : Path first middle) (tail : Path target last)
    {run : Path first last} (cut : (before.ordinary ticket).append tail=run) {p : ℕ} (dates : run.GrainDates p) :
    T.z=S.grainAt G.b p i₁ := by
  rw [←cut] at dates
  exact (((before.ordinary ticket).grainDates_append tail p).1 dates).1.2

theorem Path.grainDates_ordinary (path : Path first middle) (p : ℕ)
    (only : path.ordinaryOnly) (origin : z₀=S.grainAt G.b p i₀)
    (units : ∀i,i₀≤ i→i < i₁→S.grainAt G.b p i=S.grainAt G.b p (i+1)*G.b) :
    path.GrainDates p ∧ z₁=S.grainAt G.b p i₁ := by
  induction path with
  | here=>exact ⟨trivial,origin⟩
  | reset prev step ih=>exact only.elim
  | @ordinary W i z D z' D' src prev rate he T c n dest step ih=>
    have dated:=ih only (fun j lower upper=>units j lower (by omega))
    have age:=prev.capFactors_length
    have forward:=units i (by omega) (Nat.lt_succ_self i)
    have current := step.quantum.trans (src.grain.trans dated.2)
    refine ⟨⟨dated.1,current⟩,Nat.eq_of_mul_eq_mul_right G.base_pos ?_⟩
    exact step.grainStep.symm.trans (dated.2.trans forward)

theorem Path.grainDates_period (path : Path first middle) (p epoch : ℕ) (live : epoch<S.height)
    (start : i₀=epoch*(S.rounds+1)) (stop : i₁=(epoch+1)*(S.rounds+1))
    (origin : z₀=S.grainAt G.b p i₀) (one : path.ClosedPeriod) : path.GrainDates p := by
  cases path with
  | here=>exact one.elim
  | ordinary prev ticket=>exact one.elim
  | @reset W i z D n h C f g cut tail src prev ctl reset=>
    apply (prev.grainDates_ordinary p one origin ?_).1
    intro a lower upper
    have hEnd : i=epoch*(S.rounds+1)+S.rounds:=by rw [Nat.succ_mul] at stop;omega
    have diff : a-epoch*(S.rounds+1)<S.rounds:=by omega
    have fix : epoch*(S.rounds+1)+(a-epoch*(S.rounds+1))=a:=by omega
    simpa only [fix] using S.grain_ordinary G.b p live diff

def Path.kinds (path : Path first middle) : List Bool := by
  induction path with
  | here => exact []
  | ordinary prev step ih => exact ih ++ [false]
  | reset prev closed ih => exact ih ++ [true]


theorem Path.kinds_length (path : Path first middle) : i₀+path.kinds.length=i₁ := by
  induction path with
  | here=>simp [kinds]
  | ordinary prev ticket ih =>
    change i₀ + (prev.kinds ++ [false]).length = _ + 1
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    exact congrArg (· + 1) ih
  | reset prev closed ih =>
    change i₀ + (prev.kinds ++ [true]).length = _ + 1
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    exact congrArg (· + 1) ih

theorem Path.kinds_append (x : Path first middle) (y : Path middle last) :
    (x.append y).kinds=x.kinds++y.kinds := by
  induction y with
  | here=>simp [append,kinds]
  | ordinary prev step ih =>
    change (x.append prev).kinds ++ [false] = x.kinds ++ (prev.kinds ++ [false])
    rw [ih, List.append_assoc]
  | reset prev step ih =>
    change (x.append prev).kinds ++ [true] = x.kinds ++ (prev.kinds ++ [true])
    rw [ih, List.append_assoc]

theorem Path.kinds_ordinary (path : Path first middle) (only : path.ordinaryOnly) :
    path.kinds=List.replicate path.kinds.length false := by
  induction path with
  | here=>rfl
  | ordinary prev step ih=>
    change prev.kinds ++ [false] = List.replicate (prev.kinds ++ [false]).length false
    simp only [List.length_append, List.length_singleton, List.replicate_succ']
    exact congrArg (fun l => l ++ [false]) (ih only)
  | reset prev step ih=>exact only.elim

theorem Path.kinds_period (path : Path first middle) (count : ℕ) (span : i₁=i₀+count+1)
    (only : path.ClosedPeriod) : path.kinds=kindPeriod count := by
  cases path with
  | here=>exact only.elim
  | ordinary prev step=>exact only.elim
  | reset prev step=>
    have total:=prev.kinds_length
    have actual:prev.kinds.length=count:=by omega
    exact congrArg (fun l=>l++[true]) ((prev.kinds_ordinary only).trans (congrArg (fun n=>List.replicate n false) actual))

theorem OrdinaryLink.kind_on_cut {z' D' : ℕ} {u : ℝ} {he : 0≤ε}
    {T : StageInput W₁ G u ε} {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i₁+1) z' D' w h₀}
    (ticket : OrdinaryLink middle he T c n target) (before : Path first middle) (tail : Path target last)
    {run : Path first last} (cut : (before.ordinary ticket).append tail=run) {schedule : List Bool} (auth : run.kinds=schedule) :
    (schedule.drop (i₁-i₀)).head?=some false := by
  rw [←auth,←cut,Path.kinds_append]
  change (((before.kinds++[false])++tail.kinds).drop (i₁-i₀)).head?=_
  rw [List.append_assoc,List.drop_left' (by have:=before.kinds_length;omega)]; rfl

theorem reset_kind_on_cut {n h C f g limit finish : ℕ}
    {ctl : ResetRates G S k D₁ n h C f g limit finish} (ticket : ClosedReset middle ctl)
    (before : Path first middle) (tail : Path ticket.next last) {run : Path first last}
    (cut : (before.reset ticket).append tail=run) {schedule : List Bool} (auth : run.kinds=schedule) :
    (schedule.drop (i₁-i₀)).head?=some true := by
  rw [←auth,←cut,Path.kinds_append]
  change (((before.kinds++[true])++tail.kinds).drop (i₁-i₀)).head?=_
  rw [List.append_assoc,List.drop_left' (by have:=before.kinds_length;omega)]; rfl


end
end Hierarchy.DescentSixParty.Chronology

end OAI
