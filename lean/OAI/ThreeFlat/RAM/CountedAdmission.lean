import OAI.ThreeFlat.RAM.CountedProcedure
import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # Admission of every actual record in a counted native procedure -/

namespace ThreeFlat.RAM.TickStageSpec
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure TickFuel
variable {w : ℕ} {F : Type*} [Semiring F]

/-- A malformed record can occur anywhere in a raw sequence. Successful earlier visits
carry the remaining-record predicate into the next call. The first failing body returns
zero for every longer fuel, even inside an arbitrary linked program. -/
theorem counted (field : FieldCode F w) (body : Procedure w) (cell : Word w) (cost : ℕ)
    (inv good localOK : ℕ → Memory w → Prop)
    (step : ∀ z m, inv (z+1) m → (m cell.val).val=z+1 →
      Admission field body.block body.publicData
        (fun x => x=writeMemory m cell (m cell.val-1)) (fun _ => localOK z m)
        (fun _ out => (out cell.val).val=z ∧ inv z out ∧ (good z out ↔ good (z+1) m)) cost)
    (needed : ∀ z m,inv (z+1) m → good (z+1) m → localOK z m)
    (finished : ∀ m,inv 0 m → good 0 m) (n : ℕ) :
    Admission field (body.counted cell).block (body.counted cell).publicData
      (fun m => inv n m ∧ (m cell.val).val=n) (good n) (fun _ out => inv 0 out)
      (n*(7+cost)+4) := by
  intro P R K M pc reg pub exit installed data
  let : NeZero (body.counted cell).labels := ⟨by change 7+body.labels≠0; omega⟩
  have root : (Fin.castAddEmb body.labels) (0 : Fin 7) = (0 : Fin (body.counted cell).labels) := by
    apply Fin.ext
    change (0 : Fin 7).val = (0 : Fin (body.counted cell).labels).val
    simp
  let inner := body.block.reindex (Fin.natAddEmb 3) id
  let ip := (Fin.natAddEmb 7).trans pc
  have rom : inner.Installed M ip reg pub (pc 0) := by
    intro i
    rw [show ip i = pc (Fin.natAdd 7 i) by rfl]
    have row := installed (Fin.natAdd 7 i)
    simp only [Procedure.counted,CompressorIteration.block,Fin.addCases_right] at row
    exact row.trans (congrArg (fun stop => inner.emit ip reg pub stop i) (congrArg pc root))
  have nested := (body.block.reindex_installed (Fin.natAddEmb 3) id M ip reg pub (pc 0)).mp rom
  intro c m entry initial
  change c.pc=pc 0 at entry
  obtain ⟨hi,hc⟩ := initial
  induction n generalizing c m with
  | zero =>
    obtain ⟨d,run,done⟩ := (CompressorIteration.visit cell inner (Fin.castAddEmb body.registers)
      M pc reg pub exit installed c m entry).1 (Fin.ext hc)
    exact ⟨fun _ => ⟨4,by simp,d,m,done,hi,run⟩,fun no => (no (finished m hi)).elim⟩
  | succ n ih =>
    have nz : m cell.val≠0 := by intro h; simp [h] at hc
    obtain ⟨d,head,next⟩ := (CompressorIteration.visit cell inner (Fin.castAddEmb body.registers)
      M pc reg pub exit installed c m entry).2 nz
    have outcome := step n m hi hc M ip ((Fin.natAddEmb 3).trans reg) (pub ∘ id) (pc 0)
      nested data d _ next rfl
    have limit : (n+1)*(7+cost)+4=7+cost+(n*(7+cost)+4) := by rw [Nat.succ_mul]; omega
    rw [limit]
    by_cases current : localOK n m
    · obtain ⟨t,ht,d',out,back,⟨cn,io,good_iff⟩,run⟩ := outcome.1 current
      obtain ⟨pass,reject⟩ := ih d' out back io cn
      refine ⟨?_,?_⟩
      · intro yes
        obtain ⟨s,hs,d'',finalMem,done,iend,tail⟩ := pass (good_iff.mpr yes)
        exact ⟨7+t+s,by omega,d'',finalMem,done,iend,advance_trans (advance_trans head run) tail⟩
      · intro no
        have halt : Returns field M.program (n*(7+cost)+4) d' out 0 :=
          reject (fun ok => no (good_iff.mp ok))
        exact (halt.prefix (advance_trans head run)).later (by omega)
    · refine ⟨fun yes => (current (needed n m hi yes)).elim,fun _ => ?_⟩
      have halt : Returns field M.program cost d (writeMemory m cell (m cell.val-1)) 0 :=
        outcome.2 current
      exact (halt.prefix head).later (by omega)

end ThreeFlat.RAM.TickStageSpec

end OAI
