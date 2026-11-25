import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.PhysicalInputCopy
import OAI.ThreeFlat.RAM.PhysicalScanLink
import OAI.ThreeFlat.RAM.PackWordBlock

namespace OAI
/-! # Executable copy, pack and word-generation phases with exact public operands -/

namespace ThreeFlat.RAM.PhysicalInputPhases

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalProcedure Diagonal.TraceAddressRecord
open scoped Fin.CommRing

variable {w k : ℕ}

def copying (w src count dst : ℕ) : Procedure w :=
  ⟨10,5,3,PhysicalInputCopy.block w,PhysicalInputCopy.parameters src count dst⟩

theorem copying_spec (src n dst : ℕ) (srcFit : src+n<2^w) (dstFit : dst+n<2^w)
    (safe : dst ≤ src ∨ src+n≤dst) :
    (copying w src n dst).Spec (fun _ => True)
      (fun m m' => m'=PhysicalInputCopy.copied src n dst m) (6+5*n) := by
  intro P R K M pc reg pub exit installed data c m start _
  exact ⟨_,le_rfl,_,_,PhysicalInputCopy.advance_copy M pc reg pub exit src n dst installed data
    srcFit dstFit safe c m start,PhysicalInputCopy.finalConfig_pc ..,rfl⟩

def writing (e : Term w k 1) (data : Fin k → Word w) (lo n : ℕ) : Procedure w :=
  ⟨6+e.labels,4+e.binds,k,PhysicalScan.block e lo n,data⟩

theorem writing_spec (e : Term w k 1) (data : Fin k → Word w) (lo n : ℕ)
    (stop : lo+n<2^w) (pre : Memory w → Prop) (word : ℕ → Word w)
    (correct : ∀ m₀, pre m₀ → ∀ (a : Word w) (m : Memory w), lo≤a.val → a.val<lo+n →
      agreesOutside lo (lo+n) m m₀ → e.eval data m (fun _=>a)=word a.val) :
    (writing e data lo n).Spec pre (fun m m' => m'=fillSegment lo n word m)
      (4+n*(2*e.binds+4)) := by
  intro P R K M pc reg pub exit installed params c m start hm
  let φ : Fin k → Fin K := pub
  have he : M.publicData ∘ φ=data := funext params
  obtain ⟨u,hu,out,hpc,run⟩ := PhysicalScan.advance_block e lo n stop pc reg φ exit M installed
    c m start word (fun a mem ha hb keep => by rw [he]; exact correct m hm a mem ha hb keep)
  exact ⟨u,hu,out,_,run,hpc,rfl⟩

def packing (w src dst count : ℕ) : Procedure w :=
  ⟨15,8,4,PackWordBlock.block w,fun i => ((![src,dst,dst+count,w] i : ℕ) : Word w)⟩

theorem packing_spec_disjoint {F : Type*} [CommSemiring F] {q : ℕ} (N : BitNetwork F q)
    (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (apart : dst+FixedTraceImage.count N ≤ src ∨ src+w*FixedTraceImage.count N ≤ dst)
    (dstFit : dst+FixedTraceImage.count N < 2^w) (fit : src+w*FixedTraceImage.count N<2^w) :
    (packing w src dst (FixedTraceImage.count N)).Spec
      (fun m => ∀ i,m (src+i.val)=((FixedTraceImage.parameter N code R i).toNat : Word w))
      (fun m m' => m'=FixedTraceImage.packed N code R dst m) (FixedTraceImage.count N*(5*w+6)+6) := by
  intro P r K M pc reg pub exit installed data c m start bits
  obtain ⟨out,h,atExit⟩ := PackWordBlock.advance_disjoint M pc reg pub exit installed N code R src dst
    c m start data apart dstFit fit bits
  exact ⟨_,le_rfl,out,_,h,atExit,rfl⟩

theorem packing_spec {F : Type*} [CommSemiring F] {q : ℕ} (N : BitNetwork F q)
    (code : FieldCode F w) (R : Fin q → Record) (src dst : ℕ)
    (apart : dst+FixedTraceImage.count N ≤ src) (fit : src+w*FixedTraceImage.count N<2^w) :
    (packing w src dst (FixedTraceImage.count N)).Spec
      (fun m => ∀ i,m (src+i.val)=((FixedTraceImage.parameter N code R i).toNat : Word w))
      (fun m m' => m'=FixedTraceImage.packed N code R dst m) (FixedTraceImage.count N*(5*w+6)+6) :=
  packing_spec_disjoint N code R src dst (.inl apart) (by omega) fit


end ThreeFlat.RAM.PhysicalInputPhases

end OAI
