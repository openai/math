import OAI.ThreeFlat.Diagonal.CompressorSweepImage
import OAI.ThreeFlat.Diagonal.CompressorSweepSimulation

namespace OAI
/-! # The actual in-place native greedy sweep in the old graph's public vertex order -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast
variable {V A : Type*} [DecidableEq V] [DecidableEq A] {w N : ℕ}

def vertexAddress (b : V ≃ Fin N) (start : ℕ) (v : V) : Word w := ((start+(b v).val:ℕ):Word w)

omit [DecidableEq V] in
theorem vertexAddress_val (b : V ≃ Fin N) (start : ℕ) (fit : start+N≤2^w) (v : V) :
    (vertexAddress (w := w) b start v).val=start+(b v).val :=
  Fin.val_cast_of_lt ((Nat.add_lt_add_left (b v).isLt _).trans_le fit)

theorem inPlace_scan (b : V ≃ Fin N) (start : ℕ) (fit : start+N<2^w) (input : Memory w)
    (choices : List A) (fallback : A) (bans : V → (V → A) → List A)
    (word : A → Word w) (original : V → A)
    (row : Word w → Memory w → Word w)
    (blank : ∀ v,input (start+(b v).val)=word (original v))
    (step : ∀ alt table v,agreesOutside start (start+N) alt input →
      (∀ y,alt (start+(b y).val)=word (table y)) →
      row (vertexAddress b start v) alt=word (Ordered.pick (bans v table) fallback choices)) :
    let out:=sweep row N (start:Word w) input
    let table:=Ordered.scan (List.ofFn b.symm) choices fallback bans original
    agreesOutside start (start+N) out input ∧ ∀v,out (start+(b v).val)=word (table v) := by
  let addr:=vertexAddress (w:=w) b start
  let vs:=List.ofFn b.symm
  have hv (v : V) : (addr v).val=start+(b v).val := vertexAddress_val b start fit.le v
  have injective : Function.Injective addr := by
    intro u v equal
    apply b.injective
    apply Fin.ext
    exact Nat.add_left_cancel (by simpa only [hv] using congrArg Fin.val equal)
  have consecutive : Consecutive addr (start:Word w) vs := by
    apply consecutive_of_get
    intro i
    simp [vs,addr,vertexAddress,List.get_eq_getElem,List.getElem_ofFn]
  let fixed:=fun alt=>agreesOutside start (start+N) alt input
  have keep : ∀ alt v z, fixed alt → fixed (writeMemory alt (addr v) z) := by
    intro alt v z prior i outside
    have differ : i≠(addr v).val := by
      rw [hv]; have h:=(b v).isLt; rcases outside with lo|hi <;> omega
    simp [writeMemory,differ,prior i outside]
  have result:=sweep_scan choices fallback bans addr injective word row fixed keep
    (fun alt table v imm rep=>step alt table v imm (fun y=>by simpa only [hv] using rep y))
    vs (start:Word w) input original consecutive (fun _ _=>rfl)
    (fun v=>by rw [hv];exact blank v)
  have length : vs.length=N := by simp [vs]
  refine ⟨?_,?_⟩
  · simpa only [length] using result.1
  · intro v
    simpa only [length,hv] using result.2 v

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
