import OAI.Hierarchy.ProtocolRAMPurchaseMarketStep
import OAI.Hierarchy.ProtocolRAMPurchaseFlagPack

namespace OAI
/-! # Native sweep and joint decision table for one frozen purchase phase -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators

noncomputable section
variable {z d k : ℕ}

def program (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) : Procedure (wordBits z d copies) :=
  (ProtocolRAMFrozenSweep.program (fun i : Key z d k => sh.stageProgram S depth i)
    (List.finRange (count z d k))).seq
    (ProtocolRAMPurchaseFlagPack.code (wordBits z d copies) (fun i : Key z d k => sh.flagBank S depth i)
      (paths z S.degree depth) (sh.flagsBase S z d k depth))

def clock (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :=
  (∑ i : Key z d k, sh.stageClock S depth i) + 4 +
    ProtocolRAM.clock (ProtocolRAMPurchaseFlagPack.passes (fun i : Key z d k => sh.flagBank S depth i)
      (paths z S.degree depth) (sh.flagsBase S z d k depth))

section
attribute [local irreducible] CheapCode

private theorem cheap_sweep {w : ℕ} {I : Type*} (cpu : I → Procedure w)
    (admissible : ∀ i, CheapCode (cpu i)) (order : List I) :
    CheapCode (ProtocolRAMFrozenSweep.program cpu order) := by
  induction order with
  | nil => exact @ProtocolRAM.program_cheap w []
  | cons i rest ih =>
    exact @cheap_seq w (cpu i) (ProtocolRAMFrozenSweep.program cpu rest) (admissible i) ih

theorem cheap (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :
    CheapCode (sh.program S z d k depth) := by
  unfold program
  refine @cheap_seq (wordBits z d copies) _ _ ?_
    (ProtocolRAMPurchaseFlagPack.cheap (wordBits z d copies)
      (fun i : Key z d k => sh.flagBank S depth i) (paths z S.degree depth) (sh.flagsBase S z d k depth))
  apply cheap_sweep
  intro i
  let t := stage i
  let c := sh.cfg S depth i
  unfold stageProgram
  exact @cheap_seq (wordBits z d copies) _ _ (PurchaseTape.cheap_signed (embedded S t c) (sign S t c) (axis i)
    (wordBits z d copies) (2^z) (Fintype.card (stageAt z d t).Group) (stageAt z d t).span depth)
    (PurchaseStage.dispatch_cheap (sh.desc S depth i) (wordBits z d copies))
end

private theorem hi_le_flags (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :
    sh.hi S depth i ≤ sh.flagsBase S z d k depth :=
  (sh.final_after S depth i).trans (Nat.le_add_right ..)

theorem frozenStepAt (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (initial : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (enc : ∀ i : Key z d k, StageEncoding i)
    (ct : ∀ i,(sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) (enc i) frozen) :
    ProtocolRAMFrozenSweep.StepAt (fun i : Key z d k => sh.stageProgram S depth i)
      (sh.stageClock S depth) (fun i=>sh.stageImage S π depth i (enc i)) (sh.Untouched (k:=k) S depth frozen) (sh.Prepared S depth fixture)
      (sh.Views S π depth phase T kind frozen) := by
  intro i m common prepared
  let out:=sh.stageImage S π depth i (enc i) m
  obtain ⟨ran,seen,frame⟩ := sh.one_at S π depth hd phase T kind frozen fixture input i m common prepared (initial i) (enc i) (ct i)
  have keep (j : Key z d k) (ne : j≠i) (a : ℕ) (low : sh.lo S depth j≤a)
      (high : a<sh.hi S depth j) : out a=m a := by
    apply frame
    rcases sh.separate S depth ne with sep|sep
    · exact Or.inl (high.trans_le sep)
    · exact Or.inr (sep.trans low)
  refine ⟨ran,?_,seen,?_,?_⟩
  · intro a outside
    refine (frame a ?_).trans (common a outside)
    rcases outside with low|high
    · exact Or.inl (low.trans_le (Nat.le_add_right ..))
    · exact Or.inr ((hi_le_flags sh S depth i).trans ((Nat.le_add_right ..).trans high))
  · intro j ne fresh a low high
    exact (keep j ne a low high).trans (fresh a low high)
  · intro j ne obs
    exact sh.views_ext S π depth phase T kind frozen hd j obs (keep j ne)

private theorem frozenStep (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (initial : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen) :
    ProtocolRAMFrozenSweep.Step (fun i : Key z d k => sh.stageProgram S depth i)
      (sh.stageClock S depth) (sh.Untouched (k:=k) S depth frozen) (sh.Prepared S depth fixture)
      (sh.Views S π depth phase T kind frozen) := by
  choose enc ct using input.ct
  intro i m common prepared
  exact ⟨sh.stageImage S π depth i (enc i) m,
    sh.frozenStepAt S π depth hd phase T kind frozen fixture input initial enc ct i m common prepared⟩

/-- All stage/sign plans see the common incoming stock and price table. Their local
residues and buy decisions survive the final scans that pack the buy bits contiguously. -/
theorem execute (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    ∃ out, (sh.program S z d k depth).Exec frozen out (sh.clock S z d k depth) ∧
      sh.Untouched (k:=k) S depth frozen out ∧ (∀ i : Key z d k, sh.Views S π depth phase T kind frozen i out) ∧
      ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
        out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)=
          MarkTape.encode (wordBits z d copies) ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp)) := by
  let R := paths z S.degree depth
  let base := sh.flagsBase S z d k depth
  let source := fun i : Key z d k => sh.flagBank S depth i
  obtain ⟨mid,swept,same,seen⟩ := ProtocolRAMFrozenSweep.run (fun i : Key z d k => sh.stageProgram S depth i)
    (sh.stageClock S depth) (sh.Untouched (k:=k) S depth frozen) (sh.Prepared S depth fixture)
    (sh.Views S π depth phase T kind frozen) (frozenStep sh S π depth hd phase T kind frozen fixture input prepared)
    frozen (fun _ _ => rfl) prepared
  have capacity (i : Key z d k) : R≤(source i).size := (ProtocolRAMPurchaseSampler.lt_span R).le
  obtain ⟨packed,_,_,words,frame⟩ := ProtocolRAMPurchaseFlagPack.pack source R base mid
    (fun i => sh.source_fit S depth i hd room) capacity room
  refine ⟨ProtocolRAMPurchaseFlagPack.output source R base mid,swept.then packed,?_,?_,?_⟩
  · intro a outside
    refine (frame a ?_).trans (same a outside)
    rcases outside with low|high
    · exact Or.inl (low.trans_le ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
    · exact Or.inr high
  · intro i
    apply sh.views_ext S π depth phase T kind frozen hd i (seen i)
    intro a _ high
    exact frame a (Or.inl (high.trans_le (hi_le_flags sh S depth i)))
  · intro i r
    exact (words i r).trans ((seen i).1 r)


end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
