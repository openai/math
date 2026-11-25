import OAI.ThreeFlat.RAM.TickReadIdentifiers
import OAI.ThreeFlat.RAM.TickPhase
import OAI.ThreeFlat.RAM.TickDispatch

namespace OAI
/-! # A relocatable native prefix for the seven phases of a tick -/

namespace ThreeFlat.RAM.TickPrefix

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Diagonal.TickChronology Diagonal.ApproximateImage
open scoped Fin.CommRing

abbrev Labels (w k : ℕ) (clock : Clock) := (Fin 4 × Fin 6) ⊕
  (Fin (TickPhase.program (w:=w) (k:=k) clock).labels ⊕ (Fin 6 × Bool))

abbrev Slots (w k : ℕ) (clock : Clock) := Fin 6 ⊕ (Fin 6 ⊕
  (Fin 2 ⊕ Fin (TickPhase.program (w:=w) (k:=k) clock).binds))

variable {w k p r : ℕ} {clock : Clock}

/-- The four public words hold the offsets and lengths of the two input fields. -/
structure Keys (k : ℕ) where
  teamBase : Fin k
  teamWidth : Fin k
  stepBase : Fin k
  stepWidth : Fin k

def team (reg : Slots w k clock ↪ Fin r) : Fin 6 ↪ Fin r :=
  ⟨fun i => reg (.inl i), fun _ _ h => Sum.inl.inj (reg.injective h)⟩

def step (reg : Slots w k clock ↪ Fin r) : Fin 6 ↪ Fin r :=
  ⟨fun i => reg (.inr (.inl i)), fun _ _ h => Sum.inl.inj (Sum.inr.inj (reg.injective h))⟩

def tag (reg : Slots w k clock ↪ Fin r) : Fin r := reg (.inr (.inr (.inl 0)))
def scratch (reg : Slots w k clock ↪ Fin r) : Fin r := reg (.inr (.inr (.inl 1)))

def temp (reg : Slots w k clock ↪ Fin r) :
    Fin (TickPhase.program (w:=w) (k:=k) clock).binds ↪ Fin r :=
  ⟨fun i => reg (.inr (.inr (.inr i))),
    fun _ _ h => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (reg.injective h)))⟩

def teamSite (loc : Labels w k clock → Fin p) (reg : Slots w k clock ↪ Fin r) (keys : Keys k) :
    TickReadBits.Site p r k :=
  ⟨fun i => loc (.inl (0,i)),fun i => loc (.inl (1,i)), team reg, keys.teamBase,keys.teamWidth⟩

def stepSite (loc : Labels w k clock → Fin p) (reg : Slots w k clock ↪ Fin r) (keys : Keys k) :
    TickReadBits.Site p r k :=
  ⟨fun i => loc (.inl (2,i)),fun i => loc (.inl (3,i)), step reg, keys.stepBase,keys.stepWidth⟩

private def phasePC (loc : Labels w k clock → Fin p)
    (i : Fin (TickPhase.program (w:=w) (k:=k) clock).labels) := loc (.inr (.inl i))
private def branchPC (loc : Labels w k clock → Fin p) (i : Fin 6 × Bool) := loc (.inr (.inr i))

/-- An addressed table of native instructions. The seven supplied continuation
labels may point anywhere in the enclosing machine. -/
def emit (loc : Labels w k clock → Fin p) (reg : Slots w k clock ↪ Fin r) (keys : Keys k)
    (out : Phase → Fin p) : Labels w k clock → Instr w p r k
  | .inl (0,i) => TickReadBits.header (teamSite loc reg keys).setup (team reg) (loc (.inl (1,0)))
      keys.teamBase keys.teamWidth i
  | .inl (1,i) => TickReadBits.loop (teamSite loc reg keys).loopPC (team reg) (loc (.inl (2,0))) i
  | .inl (2,i) => TickReadBits.header (stepSite loc reg keys).setup (step reg) (loc (.inl (3,0)))
      keys.stepBase keys.stepWidth i
  | .inl (3,i) => TickReadBits.loop (stepSite loc reg keys).loopPC (step reg)
      (phasePC loc (TickPhase.program clock).first) i
  | .inr (.inl i) => (TickPhase.program clock).emit (phasePC loc) (fun _ => step reg 2) (temp reg)
      (tag reg) (branchPC loc (0,false)) i
  | .inr (.inr i) => TickDispatch.code (branchPC loc) out (tag reg) (scratch reg) i

theorem labels_le (w k : ℕ) (clock : Clock) : Fintype.card (Labels w k clock) ≤ 229 := by
  have bound := TickPhase.program_binds (w:=w) (k:=k) clock
  simp [Labels,DescriptorExpr.Term.labels_eq]
  omega

theorem slots_le (w k : ℕ) (clock : Clock) : Fintype.card (Slots w k clock) ≤ 78 := by
  have bound := TickPhase.program_binds (w:=w) (k:=k) clock
  simp [Slots]
  omega

private theorem advance_expression (M : Machine w p r k) (e : DescriptorExpr.Term w k 1)
    (loc : Fin e.labels → Fin p) (args : Fin 1 → Fin r) (tmp : Fin e.binds ↪ Fin r)
    (dst : Fin r) (exit : Fin p) (rom : ∀ j, M.code (loc j) = e.emit loc args tmp dst exit j)
    (cfg : Config w p r) (mem : Memory w) (start : cfg.pc = loc e.first)
    (fresh : ∀ i j, args i ≠ tmp j) :
    ∃ out, advance M.program e.steps cfg mem = some (out,mem) ∧ out.pc = exit ∧
      out.reg dst = e.eval M.publicData mem (cfg.reg ∘ args) ∧
      out.persistent = cfg.persistent ∧ out.privateMem = cfg.privateMem ∧
      ∀ i, i ≠ dst → (∀ j, i ≠ tmp j) → out.reg i = cfg.reg i :=
  ⟨e.run M.publicData mem args tmp dst exit cfg,
    e.advance_emit M loc args tmp dst exit rom cfg mem start,
    e.run_pc M.publicData mem args tmp dst exit cfg,
    e.run_result M.publicData mem args tmp dst exit cfg fresh tmp.injective,
    e.run_frame M.publicData mem args tmp dst exit cfg⟩

attribute [local irreducible] TickPhase.program DescriptorExpr.Term.run DescriptorExpr.Term.emit

set_option maxHeartbeats 800000 in
/-- Executing the emitted table stops at the physical phase continuation with
the decoded identifiers and tag present and both memories intact. -/
theorem advance_emit (M : Machine w p r k) (clock : Clock)
    (loc : Labels w k clock → Fin p) (reg : Slots w k clock ↪ Fin r) (keys : Keys k)
    (out : Phase → Fin p) (rom : ∀ i, M.code (loc i) = emit loc reg keys out i)
    {d nt ns np a : ℕ} (D : Fin d → Bool) (params : Fin np → Bool)
    (oldA newA oldC newC : Fin a → Bool) (teamID stepID off S : ℕ) (hdr : ℕ → Word w)
    (layout : TickReadFields.HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC teamID stepID hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (addr : off+d+nt+ns < 2^w)
    (ft : teamID < 2^nt) (fs : stepID < 2^ns) (wt : teamID < 2^w) (ws : stepID < 2^w)
    (tb : (M.publicData keys.teamBase).val = off+d) (tw : (M.publicData keys.teamWidth).val = nt)
    (sb : (M.publicData keys.stepBase).val = off+d+nt) (sw : (M.publicData keys.stepWidth).val = ns)
    (hd : clock.groupDuration < 2^w) (hlast : clock.last < 2^w) (wide : 6 < 2^w)
    (c : Config w p r) (start : c.pc = loc (.inl (0,0))) :
    ∃ t ≤ 155+6*(nt+ns), ∃ f, advance M.program t c (initialMemory S hdr) = some (f,initialMemory S hdr) ∧
      f.pc = out (clock.phase stepID) ∧ (f.reg (team reg 2)).val = teamID ∧
      (f.reg (step reg 2)).val = stepID ∧ f.reg (tag reg) = ((clock.phase stepID).tag : Word w) ∧
      f.persistent = c.persistent ∧ f.privateMem = c.privateMem := by
  let e := TickPhase.program (w:=w) (k:=k) clock
  let m := initialMemory S hdr
  let T := teamSite loc reg keys
  let U := stepSite loc reg keys
  have ti : T.Installed M (U.setup 0) :=
    ⟨fun i => rom (.inl (0,i)),fun i => rom (.inl (1,i))⟩
  have ui : U.Installed M (phasePC loc e.first) :=
    ⟨fun i => rom (.inl (2,i)),fun i => rom (.inl (3,i))⟩
  have keep (j : Fin 6) : T.reg 2 ≠ U.reg j := reg.injective.ne (by simp)
  obtain ⟨mid,read,atExpr,hTeam,hStep,hp,hm,_⟩ :=
    TickReadBits.advance_identifiers M T U (phasePC loc e.first) ti ui keep D params oldA newA oldC newC
      teamID stepID off S hdr layout bound addr ft fs wt ws tb tw sb sw c start
  let args : Fin 1 → Fin r := fun _ => step reg 2
  have fresh (i : Fin 1) (j) : args i ≠ temp reg j := reg.injective.ne (by simp)
  obtain ⟨q,expr,entry,result,preserve⟩ := advance_expression M e (phasePC loc) args (temp reg)
    (tag reg) (branchPC loc (0,false)) (fun j => rom (.inr (.inl j))) mid m atExpr fresh
  have timeWord : mid.reg (args 0) = (stepID : Word w) := by
    have val : (mid.reg (args 0)).val = stepID := by simpa only [args,U,stepSite] using hStep
    exact Fin.ext (val.trans (Fin.val_cast_of_lt ws).symm)
  have tagWord : q.reg (tag reg) = ((clock.phase stepID).tag : Word w) :=
    result.trans (TickPhase.program_eval clock hd hlast ws M.publicData m (mid.reg ∘ args) timeWord)
  have ne : tag reg ≠ scratch reg := reg.injective.ne (by simp)
  obtain ⟨n,hn,f,branch,atOut,bp,bm,br⟩ := TickDispatch.advance_dispatch M (branchPC loc) out
    (tag reg) (scratch reg) ne (fun j => rom (.inr (.inr j))) wide _ q m entry tagWord
  have saved (i : Slots w k clock) (hi : i ≠ .inr (.inr (.inl 1)))
      (hj : i ≠ .inr (.inr (.inl 0))) (hk : ∀ j, i ≠ .inr (.inr (.inr j))) :
      f.reg (reg i) = mid.reg (reg i) :=
    (br (reg i) (reg.injective.ne hi)).trans
      (preserve.2.2 (reg i) (reg.injective.ne hj) (fun j => reg.injective.ne (hk j)))
  refine ⟨(14+6*(nt+ns)+e.steps)+n,?_,f,advance_trans (advance_trans read expr) branch,atOut,
    (congrArg Fin.val (saved (.inl 2) (by simp) (by simp) (fun _ => by simp))).trans hTeam,
    (congrArg Fin.val (saved (.inr (.inl 2)) (by simp) (by simp) (fun _ => by simp))).trans hStep,
    (br (tag reg) ne).trans tagWord,bp.trans (preserve.1.trans hp),bm.trans (preserve.2.1.trans hm)⟩
  have h := TickPhase.program_binds (w:=w) (k:=k) clock
  have hs := e.steps_eq
  change e.binds ≤ 64 at h
  omega

end ThreeFlat.RAM.TickPrefix

end OAI
