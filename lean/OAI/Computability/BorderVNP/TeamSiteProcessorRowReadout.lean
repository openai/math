import OAI.Computability.BorderVNP.TeamSiteProcessorRow
import OAI.Computability.BorderVNP.TeamSiteWitness

/-! # Reading exact signed witnesses from a physical team processor

The physical replay reads one finite string of branch choices. Extending that
string to a supply determines the same terminal on the native row and on the
physical processor. The underlying sorter verdict also identifies valid rows
whose accumulated sign is zero and whose physical coefficient is therefore zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape TeamPrivateFragment TeamTapeHandoff
open TeamSiteChoices TeamSiteEvents
open TeamContraction.Replay (leaves mem_leaves_iff)

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- A physically valid sorter halt at its exact consumed branch string. It retains
the sign, including zero, before the accepting bit is masked by that sign. -/
def Context.checkedRun (clock : ℕ) (bits : List Bool) (sg : Option Bool) : Prop :=
  ∃ t < clock, ∃ q bank, StackRuns (replay (code P lib)) t (start,bits)
    (StackCompiler.labeledInput Layout.input X.raw) (q,[]) bank ∧ Checked q sg

/-- The physical inputs certify a native event sequence with this exact spelling
and accumulated sign. Both the frame test and the memory tests are required. -/
def Context.certified (fuel : ℕ) (bits : List Bool) (sg : Option Bool) : Prop :=
  ∃ es out, EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out ∧
    X.guard out = true ∧ X.sorted es ∧ bits = chunkBits es ∧ chunkSign (some false) es = sg

/-- The unmasked sorter verdict fixes both the actual masked halt and the
reported negative bit for every physically checked terminal label. -/
theorem checked_halt {q : Label P Q m g} {sg : Option Bool} (h : Checked q sg) :
    code P lib q = .halt sg.isSome ∧ negative q = sg.getD false := by
  obtain ⟨z,rfl,row⟩ := h
  exact ⟨by simp [code,withWeight,Routine.standalone,Routine.close,row,StackOp.rename],rfl⟩

/-- The native and physical row have the same terminal and exact spelling on
any common extension of their finite choice strings. -/
private theorem compare {u : Supply} {bits bs : List Bool} {weight : Option Bool} {pass : Prop} {clock t : ℕ}
    (h : X.Model bs weight pass clock) (left : Prefix u bits) (right : Prefix u bs)
    {q bank b} (run : StackRuns (replay (code P lib)) t (start,bits)
      (StackCompiler.labeledInput Layout.input X.raw) (q,[]) bank) (halt : code P lib q = .halt b) :
    bits = bs ∧ (b = true ↔ pass ∧ weight.isSome = true) ∧
      (∀ z, Checked q z ↔ pass ∧ z = weight) ∧ (b = true → negative q = weight.getD false) := by
  obtain ⟨t',_,q',bank',b',model,terminal,accepted,checked,sign⟩ := h
  obtain ⟨spelling,_,rfl,_⟩ := TeamSiteWitness.prefix_unique u left right run model halt terminal
  obtain rfl := StackOp.halt.inj (halt.symm.trans terminal)
  exact ⟨spelling,accepted,checked,sign⟩

/-- Every choice supply follows either a genuinely rejected physical row or an exact
native event sequence whose checked frame and sort tests determine its contribution. -/
def Context.coverage (fuel : ℕ) (envelope : List (TeamRAM.Event w) → ℕ) : Prop :=
  ∀ u : Supply,
    (∃ bs sg T, Prefix u bs ∧ X.Model bs sg False T) ∨
    (∃ es out, Prefix u (chunkBits es) ∧
      EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out ∧
      X.Model (chunkBits es) (chunkSign (some false) es)
        (X.guard out = true ∧ X.sorted es) (envelope es))

private theorem some_getD (s : Option Bool) (alive : s.isSome = true) : s = some (s.getD false) := by
  cases s <;> first | rfl | contradiction

private theorem terminal_certified {fuel : ℕ} {envelope : List (TeamRAM.Event w) → ℕ}
    (covers : X.coverage fuel envelope) {bits : List Bool} {t q bank b}
    (run : StackRuns (replay (code P lib)) t (start,bits) (StackCompiler.labeledInput Layout.input X.raw) (q,[]) bank)
    (halt : code P lib q = .halt b) :
    (b = true → X.certified fuel bits (some (negative q))) ∧
      (∀ sg, Checked q sg → X.certified fuel bits sg) := by
  let u := extend bits
  have hpBits : Prefix u bits := prefix_extend _
  rcases covers u with ⟨bs,weight,T,hp,model⟩ | ⟨es,out,hp,cert,model⟩
  · obtain ⟨_,accept,check,_⟩ := compare X model hpBits hp run halt
    exact ⟨fun hb => ((accept.mp hb).1).elim,fun sg h => (((check sg).mp h).1).elim⟩
  · obtain ⟨eq,accept,check,sign⟩ := compare X model hpBits hp run halt
    constructor
    · intro hb
      obtain ⟨⟨guard,sorted⟩,alive⟩ := accept.mp hb
      refine ⟨es,out,cert,guard,sorted,eq,?_⟩
      rw [sign hb]
      exact some_getD _ alive
    · intro sg h
      obtain ⟨⟨guard,sorted⟩,hs⟩ := (check sg).mp h
      exact ⟨es,out,cert,guard,sorted,eq,hs.symm⟩

/-- Every native endpoint replays on the same input within its event-specific
cost. The finite branch string and native signed weight are preserved. -/
def Context.forwardModels (fuel : ℕ) (envelope : List (TeamRAM.Event w) → ℕ) : Prop :=
  ∀ es out, EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out →
    X.Model (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es) (envelope es)

/-- A uniform processor clock covers every proposed endpoint's measured cost. -/
def Context.coversClock (fuel T : ℕ) (envelope : List (TeamRAM.Event w) → ℕ) : Prop :=
  ∀ es out, EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out → envelope es ≤ T

/-- The unmasked terminal dictionary contains exactly the certified native rows,
including valid paths of zero weight. -/
theorem Context.checked_iff_of_models {fuel clock : ℕ} {envelope : List (TeamRAM.Event w) → ℕ}
    (forward : X.forwardModels fuel envelope) (covers : X.coverage fuel envelope)
    (time : X.coversClock fuel clock envelope) (bits : List Bool) (sg : Option Bool) :
    X.checkedRun clock bits sg ↔ X.certified fuel bits sg := by
  constructor
  · rintro ⟨t,_,q,b,run,hq⟩
    exact (terminal_certified X covers run (checked_halt hq).1).2 sg hq
  · rintro ⟨es,out,cert,frame,sort,rfl,rfl⟩
    obtain ⟨t,ht,q,b,_,run,_,_,check,_⟩ := forward es out cert
    exact ⟨t,ht.trans_le (time es out cert),q,b,run,(check _).mpr ⟨⟨frame,sort⟩,rfl⟩⟩

/-- An actual accepting leaf has the certified event spelling and its exact
positive or negative sign. The proof compares the terminal of the full physical
processor with the native row on an extension of that same choice string. -/
theorem Context.leaf_iff_of_models {fuel clock : ℕ} {envelope : List (TeamRAM.Event w) → ℕ}
    (forward : X.forwardModels fuel envelope) (covers : X.coverage fuel envelope)
    (time : X.coversClock fuel clock envelope) (bits : List Bool) (z : Bool) :
    (bits,z) ∈ leaves (code P lib) negative clock start (StackCompiler.labeledInput Layout.input X.raw) ↔
      X.certified fuel bits (some z) := by
  rw [mem_leaves_iff]
  constructor
  · rintro ⟨t,_,q,b,run,halt,sg⟩
    exact sg ▸ (terminal_certified X covers run halt).1 rfl
  · rintro ⟨es,out,cert,frame,sort,rfl,hs⟩
    obtain ⟨t,ht,q,b,ok,run,halt,valid,_,sign⟩ := forward es out cert
    have yes := valid.mpr ⟨⟨frame,sort⟩,hs ▸ rfl⟩
    exact ⟨t,ht.trans_le (time es out cert),q,b,run,yes ▸ halt,(sign yes).trans (by rw [hs]; rfl)⟩

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
