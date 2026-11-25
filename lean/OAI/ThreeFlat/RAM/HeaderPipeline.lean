import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.HeaderScanState

namespace OAI
/-! # Pointwise memory and running-time semantics for linked header scans -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalProcedure
open Diagonal.CompressorPacking.Native
open scoped Fin.CommRing

variable {w : ℕ}

/-- A memory-only procedure together with an explicit state transformer and
its step count for each initial memory with representable scan boundaries. -/
structure Pipeline (w : ℕ) where
  program : Procedure w
  run : Memory w → Memory w
  ticks : Memory w → ℕ
  fits : Memory w → Prop
  correct (m : Memory w) : fits m →
    program.Spec (fun n => n=m) (fun _ out => out=run m) (ticks m)

def Pipeline.thenDo (A B : Pipeline w) : Pipeline w where
  program := A.program.seq B.program
  run m := B.run (A.run m)
  ticks m := A.ticks m + B.ticks (A.run m)
  fits m := A.fits m ∧ B.fits (A.run m)
  correct m h := by
    apply Procedure.Spec.mono (A:=A.program.seq B.program)
      (Procedure.Spec.seq (A:=A.program) (B:=B.program)
        (pre:=fun n=>n=m) (left:=fun _ out=>out=A.run m)
        (mid:=fun n=>n=A.run m) (right:=fun _ out=>out=B.run (A.run m))
        (ka:=A.ticks m) (kb:=B.ticks (A.run m))
        (A.correct m h.1) (B.correct (A.run m) h.2) (fun _ _ hn=>hn))
    · exact fun _ => id
    · rintro _ _ ⟨_,_,r⟩
      exact r
    · exact le_rfl

def headerWord (m : Memory w) (current : Word w) (off : ℕ) : Word w :=
  m (m current.val+(off:Word w)).val

def Pipeline.scan (current : Word w) (start length : ℕ) (e : Term w 0 1) : Pipeline w where
  program := procedure current start length e
  run m := sweep (fun a m' => e.eval Fin.elim0 m' (fun _ => a))
    (headerWord m current length).val (headerWord m current start) m
  ticks m := 11+(headerWord m current length).val*(2*e.binds+4)
  fits m := (headerWord m current start).val + (headerWord m current length).val < 2^w
  correct m cap := by
    intro P R K M pc reg φ exit installed _ c m' entry h
    subst m'
    let startWord := headerWord m current start
    let countWord := headerWord m current length
    have hs : m (m current.val+(start:Word w)).val = ((startWord.val : ℕ):Word w) := by
      exact (Fin.cast_val_eq_self startWord).symm
    have hl : m (m current.val+(length:Word w)).val = ((countWord.val : ℕ):Word w) := by
      exact (Fin.cast_val_eq_self countWord).symm
    obtain ⟨out,finish,r⟩ := block_sweep e current start length startWord.val countWord.val cap
      pc reg φ exit M installed c m entry hs hl
    have pub : (M.publicData ∘ φ : Fin 0 → Word w) = Fin.elim0 := funext fun i => i.elim0
    have values := congrArg (fun p : Fin 0 → Word w =>
      sweep (fun a m' => e.eval p m' (fun _ => a)) countWord.val (startWord.val : Word w) m) pub
    rw [Fin.cast_val_eq_self] at values
    refine ⟨_,le_rfl,out,_,r,finish,?_⟩
    simpa only [Fin.cast_val_eq_self] using values


end ThreeFlat.RAM.HeaderScan

end OAI
