import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay
import OAI.Computability.BorderVNP.RoutingISABlockAppend
import OAI.Computability.BorderVNP.TeamContractionPaths

/-!
# Factoring native returning paths at a sequence boundary

A full event records the complete choice tape consumed by its instruction, including a
private cell call. Hence two returns from the same machine state with compatible event
histories reach the same halt. This identifies the dependent sum of consecutive returns
with the returns of the sequenced program, including the sign of each private call.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Two halted prefixes of one event history agree, including the registers and memory
at the halt. The individual instructions may call private machines. -/
theorem NativePrefix.eq_of_shared_events {S : Type*} {P : S → TeamRAM.Instr w S}
    {s m es t mt fs z mz} (a : NativePrefix P s m es t mt) (ha : P t = .accept)
    (b : NativePrefix P s m fs z mz) (hb : P z = .accept)
    {tail tail' : List (TeamRAM.Event w)} (shared : es ++ tail = fs ++ tail') :
    es = fs ∧ t = z ∧ mt = mz := by
  induction a generalizing fs z mz tail tail' with
  | nil =>
    cases b with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons h _ _ => simp [ha,TeamRAM.Instr.action] at h
  | @cons s m act bits next sign rs t mt actA stepA _ ih =>
    cases b with
    | nil => simp [hb,TeamRAM.Instr.action] at actA
    | @cons _ _ act' bits' next' sign' rs' _ _ actB stepB restB =>
      obtain rfl := Option.some.inj (actA.symm.trans actB)
      have headTail := List.cons.inj shared
      obtain rfl := congrArg TeamRAM.Event.choices headTail.1
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (stepA.symm.trans stepB))
      obtain ⟨rfl,rfl,rfl⟩ := ih ha restB hb headTail.2
      exact ⟨rfl,rfl,rfl⟩

/-- Two normal returns of the same structured fragment cannot give distinct prefixes
of a common event history. -/
theorem Runs.eq_of_shared_events {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt fs z mz} (a : Runs pub macros c s m es t mt)
    (b : Runs pub macros c s m fs z mz) {tail tail' : List (TeamRAM.Event w)}
    (shared : es ++ tail = fs ++ tail') : es = fs ∧ t = z ∧ mt = mz := by
  obtain ⟨he, hs, hm⟩ := (DiagonalResidueRAM.at_last a).eq_of_shared_events
    (c.fetch_finish pub macros t) (DiagonalResidueRAM.at_last b) (c.fetch_finish pub macros z) shared
  exact ⟨he,congrArg TeamOpcode.State.reg hs,hm⟩

namespace Evaluator

/-- Normal returning executions with their chronological events, final register bank
and final shared memory. -/
def Returns (c : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :=
  {z : List (TeamRAM.Event w) × Bank w × Memory w // Runs pub macros c s m z.1 z.2.1 z.2.2}

variable (a b : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)

private def join :
    (Σ x : Returns a pub macros s m, Returns b pub macros x.val.2.1 x.val.2.2) →
    Returns (.seq a b) pub macros s m
  | ⟨x,y⟩ => ⟨⟨x.val.1 ++ y.val.1,y.val.2⟩,x.property.seq y.property⟩

/-- Joining successive runs is a bijection. The second run starts in exactly the
register bank and shared memory returned by the first. -/
noncomputable def seqReturnEquiv :
    (Σ x : Returns a pub macros s m, Returns b pub macros x.val.2.1 x.val.2.2) ≃
    Returns (.seq a b) pub macros s m := by
  apply Equiv.ofBijective (join a b pub macros s m)
  constructor
  · rintro ⟨⟨⟨es,t,mt⟩,ra⟩,⟨⟨fs,z,mz⟩,rb⟩⟩ ⟨⟨⟨es',t',mt'⟩,ra'⟩,⟨⟨fs',z',mz'⟩,rb'⟩⟩ h
    have he := congrArg Subtype.val h
    change (⟨es ++ fs,z,mz⟩ : List (TeamRAM.Event w) × Bank w × Memory w) = ⟨es' ++ fs',z',mz'⟩ at he
    obtain ⟨history,final⟩ := Prod.mk.inj he
    obtain ⟨rfl,rfl,rfl⟩ := ra.eq_of_shared_events ra' history
    obtain rfl := List.append_cancel_left history
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj final
    rfl
  · rintro ⟨⟨es,z,mz⟩,run⟩
    obtain ⟨t,mt,fs,gs,he,ra,rb⟩ := Runs.seq_iff.mp run
    exact ⟨⟨⟨⟨fs,t,mt⟩,ra⟩,⟨⟨gs,z,mz⟩,rb⟩⟩,Subtype.ext (Prod.ext he.symm rfl)⟩

/-- The chronological trace of a composed execution and both pieces of its final
state are the expected ones. -/
theorem seqReturnEquiv_val (x : Returns a pub macros s m)
    (y : Returns b pub macros x.val.2.1 x.val.2.2) :
    (seqReturnEquiv a b pub macros s m ⟨x,y⟩).val = (x.val.1 ++ y.val.1,y.val.2) := rfl

/-- The integer weight of the joined execution multiplies the signed weights of its
stages, including the signs returned by private cell programs. -/
theorem seqReturnEquiv_weight (x : Returns a pub macros s m)
    (y : Returns b pub macros x.val.2.1 x.val.2.2) :
    TeamContraction.pathWeight (seqReturnEquiv a b pub macros s m ⟨x,y⟩).val.1 =
      TeamContraction.pathWeight x.val.1 * TeamContraction.pathWeight y.val.1 := by
  rw [seqReturnEquiv_val]
  simp [TeamContraction.pathWeight]

/-- The sum over a finite family of real sequenced returns is the iterated signed
sum over first-stage runs and the second-stage runs available in each resulting state. -/
theorem seqReturn_signed_sum [Fintype (Returns a pub macros s m)]
    [∀ x : Returns a pub macros s m, Fintype (Returns b pub macros x.val.2.1 x.val.2.2)]
    [Fintype (Returns (.seq a b) pub macros s m)] :
    (∑ p : Returns (.seq a b) pub macros s m, TeamContraction.pathWeight p.val.1) =
    ∑ x : Returns a pub macros s m, ∑ y : Returns b pub macros x.val.2.1 x.val.2.2,
      TeamContraction.pathWeight x.val.1 * TeamContraction.pathWeight y.val.1 := by
  classical
  rw [← (seqReturnEquiv a b pub macros s m).sum_comp, Fintype.sum_sigma]
  simp only [seqReturnEquiv_weight]

end Evaluator
end RoutingISA

end BorderVNP
end Computability
end OAI
