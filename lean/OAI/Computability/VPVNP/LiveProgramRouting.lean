import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveStagePaths
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Native path factorization at the three header decisions

A router contributes exactly one choice-free burst. Removing that burst is a
bijection from accepting paths to accepting continuations, with the report's
memory effect, returned cursor and contribution to the cost predicate retained.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- The three routing decisions, selecting the group mode, the incoming tail preparation, or
the outgoing tail preparation. -/
inductive Router where
  | mode | firstTail | last
  deriving DecidableEq

namespace Router

/-- Stage at which the selected routing decision is executed. -/
def stage : Router → Stage
  | .mode => Stage.mode | .firstTail => Stage.firstTail | .last => Stage.last

/-- Geometry expression locating the header word that supplies this router's flag. -/
def address : Router → PublicExpr
  | .mode => HeaderLayout.mode Layout.header
  | .firstTail => HeaderLayout.firstTail Layout.header
  | .last => HeaderLayout.flag Layout.header .last

/-- Map a decoded flag ordinal to this router's acceptance, rejection, or stage-transfer
target. -/
def target : Router → Fin 3 → Route.Target
  | .mode => modeTarget | .firstTail => firstTarget | .last => lastTarget

/-- The router's two evaluated operands, the address of its decision flag and the address of
the outer stage tag. -/
def data (r : Router) (g : Geometry) (lit : LiteralPrefix) : Fin 2 → Word g.w :=
  Pieces.word g lit ∘ InputOperand.geometry ∘ StageOperands.router r.address

theorem terminal (r : Router) (p : UniversalMachine.Program) : next p r.stage = none := by cases r <;> rfl

theorem component (r : Router) (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) :
    HEq (Pieces.component (rows c p O) r.stage g lit) (((Route.table r.target).instantiate g.w (r.data g lit)).program) := by
  cases r <;> rfl

private theorem source_call (r : Router) (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (hw : 2 ≤ g.w) (st : Word g.w) (m : Memory g.w) (i : Fin 3)
    (hf : m ((r.data g lit) 0).val = (i.val : Word g.w)) (bs : List Bool) (f : ℕ) :
    let P := Pieces.component (rows c p O) r.stage g lit
    execute P (f+13) (P.start st) m bs = Route.report (r.data g lit) (m ((r.data g lit) 0).val) i (r.target i) bs := by
  cases r <;> exact Route.execute_flag hw _ _ st m i hf bs f

/-- At a checked flag this is the exact linked report, including rejection on
surplus choices and every external probe of the router and the outer dispatch. -/
theorem execute (r : Router) (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (hw : 2 ≤ g.w) (fit : 21 ≤ 2^g.w)
    (st : Word g.w) (m : Memory g.w) (i : Fin 3) (hf : m ((r.data g lit) 0).val = (i.val : Word g.w))
    (addr : Word g.w := Pieces.word g lit (.geometry Layout.stageTag))
    (ha : addr = Pieces.word g lit (.geometry Layout.stageTag) := by rfl)
    (ht : m addr.val = LiveStageLink.tagWord g.w r.stage) (bs : List Bool) (f : ℕ) :
    let P := (machine c p O g lit).program
    BurstRAM.execute P (f+13+(LiveStageLink.dispatchEvents addr r.stage).length) (P.start st) m bs =
      (Route.report (r.data g lit) (m ((r.data g lit) 0).val) i (r.target i) bs).map
        (LiveStageLink.linkedReport (next p) addr r.stage) := by
  subst addr
  dsimp only
  let rows' := rows c p O
  let tag := Pieces.word g lit (.geometry Layout.stageTag)
  let bank := Pieces.word g lit ∘ Pieces.bank rows'
  unfold LiveProgram.machine
  unfold Pieces.machine Pieces.program
  rw [Pieces.data_eq]
  change BurstRAM.execute (LiveStageLink.machine (Pieces.table rows') (next p) bank tag).program
    (f+13+(LiveStageLink.dispatchEvents tag r.stage).length) ((LiveStageLink.machine (Pieces.table rows') (next p) bank tag).program.start st) m bs = _
  rw [LiveStageLink.execute_linked (Pieces.table rows') (next p) bank tag r.stage fit st (f+13) m ht bs,
    Pieces.component_eq]
  have hc := source_call r c p O g lit hw st m i hf bs f
  rw [← hc]
  generalize he : BurstRAM.execute (Pieces.component rows' r.stage g lit) (f+13)
    ((Pieces.component rows' r.stage g lit).start st) m bs = q
  cases q with
  | none => rfl
  | some rep =>
    have hlen := (execute_spec he).1.length_lt
    have hx : LiveStageLink.exitReport (next p) tag r.stage rep = rep := by
      cases rep with | mk es out => cases out <;> simp [LiveStageLink.exitReport,terminal]
    change ((some rep).bind (LiveStageLink.boundedExit (next p) tag r.stage (f+13))).map _ =
      (some rep).map (LiveStageLink.linkedReport (next p) tag r.stage)
    simp [LiveStageLink.linkedReport,LiveStageLink.boundedExit,hx,hlen]

end Router

/-- The remaining calls use the precise memory and persistent word produced by
this deterministic burst. A terminal burst allows only the empty remainder. -/
abbrev Continuations {w : ℕ} {C : Type*} (P : BurstRAM.Program w C) (fuel : ℕ) (m : Memory w)
    (rep : Report w) (cap : List (Report w) → Prop) :=
  {bits : List (List Bool) // ∃ logs,
    runSegment P fuel rep.result (after m rep.events) bits = some logs ∧
    endState rep.result logs = none ∧ cap (rep::logs)}

/-- A known successful choice-free first call is the unique first call on any
accepting path. This statement permits arbitrary clocks and report-dependent caps. -/
noncomputable def deterministicEquiv {w : ℕ} {C : Type*} (P : BurstRAM.Program w C) (f : ℕ) (st : Word w) (m : Memory w)
    (rep : Report w) (call : BurstRAM.execute P f (P.start st) m [] = some rep)
    (cap : List (Report w) → Prop) : Continuations P f m rep cap ≃ ActualPaths P f st m cap := by
  let add : Continuations P f m rep cap → ActualPaths P f st m cap := fun path => ⟨[]::path.val, by
    obtain ⟨logs,hr,hh,hc⟩ := path.property
    exact ⟨rep::logs,by simp [runSegment,call,hr],hh,hc⟩⟩
  apply Equiv.ofBijective add
  constructor
  · intro a b hab
    exact Subtype.ext (List.cons.inj (congrArg Subtype.val hab)).2
  · rintro ⟨bs,logs,hr,hh,hc⟩
    cases bs with
    | nil => simp [runSegment] at hr; subst logs; contradiction
    | cons x xs =>
      rw [runSegment] at hr
      cases hx : BurstRAM.execute P f (P.start st) m x with
      | none => simp [hx] at hr
      | some a =>
        obtain ⟨hx',ha⟩ := execute_prefix_unique call (suffix := x) (by simpa using hx)
        subst x a
        simp only [call,Option.map_eq_some_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        exact ⟨⟨xs,tail,ht,hh,hc⟩,rfl⟩

/-- Native path bijection at any of the live program's three decisions. -/
noncomputable def Router.pathEquiv (r : Router) (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (hw : 2 ≤ g.w) (fit : 21 ≤ 2^g.w)
    (st : Word g.w) (m : Memory g.w) (i : Fin 3) (hf : m ((r.data g lit) 0).val = (i.val : Word g.w))
    (ht : m (Pieces.word g lit (.geometry Layout.stageTag)).val = LiveStageLink.tagWord g.w r.stage)
    (f : ℕ) (src : Report g.w)
    (selected : Route.report (r.data g lit) (m ((r.data g lit) 0).val) i (r.target i) [] = some src)
    (cap : List (Report g.w) → Prop) :
    let P := (machine c p O g lit).program
    let addr := Pieces.word g lit (.geometry Layout.stageTag)
    let clock := f+13+(LiveStageLink.dispatchEvents addr r.stage).length
    Continuations P clock m (LiveStageLink.linkedReport (next p) addr r.stage src) cap ≃ ActualPaths P clock st m cap := by
  apply deterministicEquiv
  rw [r.execute c p O g lit hw fit st m i hf _ rfl ht [] f,selected]
  rfl

end LiveProgram

end VPVNP
end Computability
end OAI
