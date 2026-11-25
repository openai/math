import OAI.ThreeFlat.RAM.TracePrototypeHeader
import OAI.ThreeFlat.RAM.EffectSeedProcedure
import OAI.ThreeFlat.RAM.CountedProcedure
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # Physical startup of the compact selected H trace reader -/
namespace ThreeFlat.RAM.TracePrototypeBoot
open Computability.VPVNP.BurstRAM PhysicalProcedure Diagonal.TickWorkspace EffectStream Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {W : ℕ}

structure Args (W : ℕ) where
  templateSource : ℕ
  templateCount : ℕ
  seedCount : ℕ
  reader : Fin FixedTraceProgram.P→Word W

def Args.seedSource (A : Args W) := A.templateSource+W*A.templateCount

def readerLayout (u : ℕ) : TraceRawLookup.Layout := ⟨base u 52,0,base u 57⟩

def Args.procedure (A : Args W) (u : ℕ) : Procedure W :=
  ((PhysicalInputPhases.packing W A.templateSource (base u 53) A.templateCount).seq
    (EffectSeed.procedure W A.seedSource (base u 58) A.seedCount)).seq
    (TraceRawLookup.install (readerLayout u) A.reader)

def Args.budget (A : Args W) :=
  (A.templateCount*(5*W+6)+6) + (2*A.seedCount*(5*W+6)+6+(4+6*A.seedCount)) +
    (4+FixedTraceProgram.P*(2*(3*FixedTraceProgram.P+1)+4))

def headerWords {F : Type*} [CommSemiring F] {q : ℕ} (G : BitNetwork F q)
    (code : FieldCode F W) (u pins shared : ℕ) : Fin FixedTraceProgram.P→Word W :=
  Fin.append (fun _ : Fin 2=>0) (Fin.append (fun _ : Fin 5=>0)
    (FixedTraceProgram.publicWords G code pins shared (base u 52) (base u 53) (base u 53+11*G.cells)))

@[simp] theorem headerWords_extra {F : Type*} [CommSemiring F] {q : ℕ} (G : BitNetwork F q)
    (code : FieldCode F W) (u pins shared : ℕ) (i : Fin 11) :
    headerWords G code u pins shared (FixedTraceProgram.extra i) =
      FixedTraceProgram.publicWords G code pins shared (base u 52) (base u 53) (base u 53+11*G.cells) i := by
  simp only [headerWords,FixedTraceProgram.extra,Fin.append_right]

def cursor {F : Type*} [CommSemiring F] {q : ℕ} (u parameterBase directoryWords pins shared seedCount : ℕ)
    (G : BitNetwork F q) (code : FieldCode F W) : Args W :=
  ⟨parameterBase+W*directoryWords,FixedTraceImage.count G,seedCount,headerWords G code u pins shared⟩

def Args.image {F : Type*} [CommSemiring F] {q : ℕ} (A : Args W) (u : ℕ) (G : BitNetwork F q)
    (code : FieldCode F W) (keys : Fin q→Diagonal.TraceAddressRecord.Record) (es : List (EffectStream.Record W))
    (m : Memory W) :=
  TraceRawLookup.installed (readerLayout u) A.reader
    (after (fillSegment (base u 58) (2*es.length) (packedWord (base u 58) es)
      (FixedTraceImage.packed G code keys (base u 53) m)) (events es))

theorem Args.run {F : Type*} [CommSemiring F] {q : ℕ} (A : Args W) (u : ℕ) (G : BitNetwork F q)
    (code : FieldCode F W) (keys : Fin q→Diagonal.TraceAddressRecord.Record) (es : List (EffectStream.Record W))
    (tcount : A.templateCount=FixedTraceImage.count G) (scount : A.seedCount=es.length)
    (low : A.seedSource+W*(2*es.length)≤base u 53)
    (end53 : base u 53+FixedTraceImage.count G<2^W)
    (end58 : base u 58+2*es.length<2^W) (end57 : base u 57+FixedTraceProgram.P<2^W)
    (safe : EffectStream.Safe (base u 58) es) :
    (A.procedure u).Spec (fun m=>(∀ i,m (A.templateSource+i.val)=((FixedTraceImage.parameter G code keys i).toNat:Word W)) ∧
       EffectSeed.Input A.seedSource (base u 58) es m)
      (fun m out=>out=A.image u G code keys es m) A.budget := by
  have seedAfter : A.templateSource+W*FixedTraceImage.count G=A.seedSource:=by simp [Args.seedSource,tcount]
  have ord : base u 53≤base u 58:=by dsimp [base];omega
  simp only [Args.procedure, Args.budget, tcount, scount]
  intro pcN regN pubN M pc reg pub exit rom data cfg input entry ok
  let packed := FixedTraceImage.packed G code keys (base u 53) input
  have pack : (PhysicalInputPhases.packing W A.templateSource (base u 53) (FixedTraceImage.count G)).Spec
      (·=input) (fun _ out=>out=packed) (FixedTraceImage.count G*(5*W+6)+6) :=
    Procedure.Spec.atMemory
      (PhysicalInputPhases.packing_spec_disjoint G code keys A.templateSource (base u 53)
        (.inr (by omega)) end53 (by omega)) input ok.1
  have seed : (EffectSeed.procedure W A.seedSource (base u 58) es.length).Spec
      (EffectSeed.Input A.seedSource (base u 58) es)
      (fun m o=>o=after (fillSegment (base u 58) (2*es.length) (packedWord (base u 58) es) m) (events es))
      (2*es.length*(5*W+6)+6+(4+6*es.length)) :=
    EffectSeed.seed_spec A.seedSource (base u 58) es (.inr (by omega)) end58 (by omega) safe
  have setup : EffectSeed.Input A.seedSource (base u 58) es packed :=by
    intro i hi j hj
    have hit:=Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
    have stop:A.seedSource+W*i+j<base u 53:=by rw [Nat.mul_succ] at hit;omega
    simpa [packed,FixedTraceImage.packed,fillSegment,Nat.not_le.mpr stop] using ok.2 i hi j hj
  refine Procedure.Spec.mono (Procedure.Spec.seq (Procedure.Spec.seq (A:=PhysicalInputPhases.packing W
      A.templateSource (base u 53) (FixedTraceImage.count G)) (B:=EffectSeed.procedure W A.seedSource (base u 58) es.length)
      pack seed (fun _ out h=>h.symm ▸ setup)) (TraceRawLookup.install_spec (readerLayout u) A.reader end57)
      (fun _ _ _=>trivial)) (pre':=(·=input))
      (post':=fun _ out=>out=A.image u G code keys es input) (fun _ h=>h) ?_ le_rfl
      M pc reg pub exit rom data cfg input entry rfl
  rintro m out ⟨afterSeed,⟨afterPack,rfl,rfl⟩,rfl⟩
  rfl

theorem Args.resources (A : Args W) (u : ℕ) :
    (A.procedure u).labels+(A.procedure u).registers+(A.procedure u).slots≤400 := by
  have z:=TraceRawLookup.installed_resources (readerLayout u) A.reader
  simp only [Args.procedure,Procedure.seq,EffectSeed.procedure,EffectSeed.scatter,PhysicalInputPhases.packing]
  omega


end ThreeFlat.RAM.TracePrototypeBoot

end OAI
