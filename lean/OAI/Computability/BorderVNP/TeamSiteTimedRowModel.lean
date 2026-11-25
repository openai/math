import OAI.Computability.BorderVNP.TeamSiteTimedChunk
import OAI.Computability.BorderVNP.TeamSiteProcessorRowReadout

/-! # Reading a true timed RAM certificate from a physical site terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape BurstRAM TeamPrivateFragment TeamTapeHandoff TeamSiteChoices TeamSiteEvents
open TeamContraction.Replay (leaves mem_leaves_iff)
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
/-- The parsed site context uses the ordinary physical port layout widened by the trusted timer tape. -/
abbrev Site (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ) (n d e w : ℕ) :=
  Processor.Row.Context P (fun j => extend (lib j) (mark j)) n d e w

variable (X : Site P lib mark n d e w)

/-- The genuine unmasked sorter terminal, including valid zero-weight rows. -/
def Checked (q : Label P Q m g) (sg : Option Bool) : Prop :=
  ∃ z, q = .site (.sort sg (some z)) ∧ TeamTapeInputRoute.Verify.processor.body.code z = .halt true

/-- The physical prelude and whole row start at the bank with its trusted native template.
The enclosing source clock has already charged its generation. -/
def Model (bits : List Bool) (sg : Option Bool) (pass : Prop) (T : ℕ) : Prop :=
  ∃ t < T, ∃ q out b, StackRuns (replay (code P lib mark)) t (.site Processor.start,bits)
    (TrustedClock.installed Layout.input X.raw) (q,[]) out ∧ code P lib mark q = .halt b ∧
    (b = true ↔ pass ∧ sg.isSome = true) ∧
    (∀ z, Checked q z ↔ pass ∧ z = sg) ∧ (b = true → negative P q = sg.getD false)

/-- The clock envelope includes the actual timed reset cost for each call. -/
noncomputable def budget (N : ℕ) (es : List (TeamRAM.Event w)) : ℕ :=
  X.cost (TimedBudget.body m g (TimedBudget.meterCoefficient m g) N es) es

/-- A chronological row with the genuine metered native semantics. -/
abbrev Endpoint (N : ℕ) (es : List (TeamRAM.Event w)) (out : Frame w r) : Prop :=
  EndpointRow P X.pub (fun j => (lib j).timedEval (mark j) N) X.block X.limit X.cap X.frame es out

/-- A row certifies the exact branch string after validating its transmitted
frame and all occupied sorter lanes. -/
def certified (N : ℕ) (bits : List Bool) (sg : Option Bool) : Prop :=
  ∃ es out, Endpoint X N es out ∧ X.guard out = true ∧ X.sorted es ∧ bits = chunkBits es ∧ chunkSign (some false) es = sg

/-- All accepted timed rows reach their exact physical terminal. -/
def forward (N : ℕ) : Prop := ∀ es out, Endpoint X N es out →
  Model X (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es) (budget X N es)

/-- Every physical supply gives a rejected row or the checked run of a timed native endpoint. -/
def supplied (N : ℕ) : Prop := ∀ u : Supply,
  (∃ bits sg T, Prefix u bits ∧ Model X bits sg False T) ∨
  ∃ es out, Prefix u (chunkBits es) ∧ Endpoint X N es out ∧
    Model X (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es) (budget X N es)

/-- The elapsed clock of an unmasked checked timed row. -/
def checkedRun (T : ℕ) (bits : List Bool) (sg : Option Bool) : Prop :=
  ∃ t < T, ∃ q bank, StackRuns (replay (code P lib mark)) t (.site Processor.start,bits)
    (TrustedClock.installed Layout.input X.raw) (q,[]) bank ∧ Checked q sg

theorem checked_halt {q : Label P Q m g} {sg : Option Bool} (h : Checked q sg) :
    code P lib mark q = .halt sg.isSome ∧ negative P q = sg.getD false := by
  obtain ⟨z,rfl,row⟩ := h
  have old := Processor.Row.checked_halt (lib:=fun j => extend (lib j) (mark j))
    (q:=Processor.Label.sort (P:=P) (Q:=Q) (m:=m+1) (g:=g) sg (some z)) ⟨z,rfl,row⟩
  change (Processor.code P _ (.sort sg (some z))).rename TeamClocked.Port.user Label.site = _ ∧ _
  rw [old.1]
  exact ⟨rfl,rfl⟩

private theorem compare {u : Supply} {bits bs : List Bool} {weight : Option Bool} {pass : Prop} {T t : ℕ}
    (h : Model X bs weight pass T) (hbits : Prefix u bits) (hbs : Prefix u bs)
    {q bank b} (run : StackRuns (replay (code P lib mark)) t (.site Processor.start,bits)
      (TrustedClock.installed Layout.input X.raw) (q,[]) bank) (halt : code P lib mark q = .halt b) :
    bits = bs ∧ (b = true ↔ pass ∧ weight.isSome = true) ∧
      (∀ z, Checked q z ↔ pass ∧ z = weight) ∧ (b = true → negative P q = weight.getD false) := by
  obtain ⟨t',_,q',bank',b',replay,terminal,accepted,checked,sign⟩ := h
  obtain ⟨spelling,_,rfl,_⟩ := TeamSiteWitness.prefix_unique u hbits hbs run replay halt terminal
  obtain rfl := StackOp.halt.inj (halt.symm.trans terminal)
  exact ⟨spelling,accepted,checked,sign⟩

private theorem terminal {N : ℕ} (all : supplied X N) {bits : List Bool} {t q bank b}
    (run : StackRuns (replay (code P lib mark)) t (.site Processor.start,bits)
      (TrustedClock.installed Layout.input X.raw) (q,[]) bank) (halt : code P lib mark q = .halt b) :
    (b = true → certified X N bits (some (negative P q))) ∧ (∀ sg, Checked q sg → certified X N bits sg) := by
  let u := TeamSiteChoices.extend bits
  have hb : Prefix u bits := prefix_extend _
  rcases all u with ⟨bs,weight,T,pre,model⟩ | ⟨es,out,pre,row,model⟩
  · obtain ⟨_,accept,check,_⟩ := compare X model hb pre run halt
    exact ⟨fun h => ((accept.mp h).1).elim,fun sg h => (((check sg).mp h).1).elim⟩
  · obtain ⟨eq,accept,check,sign⟩ := compare X model hb pre run halt
    constructor
    · intro h
      obtain ⟨⟨guard,sort⟩,live⟩ := accept.mp h
      refine ⟨es,out,row,guard,sort,eq,?_⟩
      rw [sign h]
      cases eq : chunkSign (some false) es <;> simp_all
    · intro sg h
      obtain ⟨⟨guard,sort⟩,weight⟩ := (check sg).mp h
      exact ⟨es,out,row,guard,sort,eq,weight.symm⟩

/-- True finite leaves coincide with certified chronological spellings and their
nonzero signs at any clock covering the admitted rows. -/
theorem leaf_iff {N T : ℕ} (emit : forward X N) (all : supplied X N)
    (clock : ∀ es out, Endpoint X N es out → budget X N es ≤ T) (bits : List Bool) (z : Bool) :
    (bits,z) ∈ leaves (code P lib mark) (negative P) T (.site Processor.start) (TrustedClock.installed Layout.input X.raw) ↔
      certified X N bits (some z) := by
  rw [mem_leaves_iff]
  constructor
  · rintro ⟨t,_,q,b,run,halt,sg⟩
    exact sg ▸ (terminal X all run halt).1 rfl
  · rintro ⟨es,out,row,guard,sort,rfl,sg⟩
    obtain ⟨t,ht,q,b,ok,run,halt,valid,_,sign⟩ := emit es out row
    have yes := valid.mpr ⟨⟨guard,sort⟩,sg ▸ rfl⟩
    exact ⟨t,ht.trans_le (clock es out row),q,b,run,yes ▸ halt,(sign yes).trans (by rw [sg]; rfl)⟩

/-- Unmasked physical checks also retain zero-weight native paths. -/
theorem checked_iff {N T : ℕ} (emit : forward X N) (all : supplied X N)
    (clock : ∀ es out, Endpoint X N es out → budget X N es ≤ T) (bits : List Bool) (sg : Option Bool) :
    checkedRun X T bits sg ↔ certified X N bits sg := by
  constructor
  · rintro ⟨t,_,q,b,run,check⟩
    exact (terminal X all run (checked_halt (lib:=lib) (mark:=mark) check).1).2 sg check
  · rintro ⟨es,out,row,guard,sort,rfl,rfl⟩
    obtain ⟨t,ht,q,b,_,run,_,_,check,_⟩ := emit es out row
    exact ⟨t,ht.trans_le (clock es out row),q,b,run,(check _).mpr ⟨⟨guard,sort⟩,rfl⟩⟩

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
