import OAI.Computability.VPVNP.CompressorGreedyRelocated
import OAI.Computability.VPVNP.CompressorLogAccess
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-! # Addresses touched by the relocated greedy initializer

The control-word prefix runs entirely in registers. The next block clears
one label and writes the two words at the beginning of the vertex record.
The final block increments the private cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.PrepareAccess

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport Compression
open scoped Fin.CommRing
open private putHeader index_add base_index base_next base_bounds nextVertex
  from OAI.Computability.VPVNP.CompressorRecordGreedyPrepare

variable {w N width d : ℕ} {V : Type*}

/-- Membership in the half-open interval of physical addresses from `lo` to `hi`. -/
def Interval (lo hi x : ℕ) := lo ≤ x ∧ x < hi

theorem head (L : WalkLayout w N width) (T : PortTables w) (m : Memory w) (i : Fin N)
    (rs : Regs w 13) (labels : T.labels = Fin.ofNat _ L.origin)
    (input : RowInput T (Fin.ofNat _ i.val) 0 rs) (unit : rs 11 = 1)
    (first : rs 8 = L.base 0) (stride : rs 9 = Fin.ofNat _ (2+width))
    {es : List (Event w)} {out : Regs w 13} {mem : Memory w}
    (run : trace (slotNumbers w d) (Fin.ofNat _ i.val) (putHeader d) rs m = some (es,out,mem)) :
    Reads (fun _ ↦ False) es ∧ Writes (Interval L.origin L.limit) es := by
  have lab : T.labels+Fin.ofNat _ i.val = L.label i := by rw [labels,index_add]; rfl
  have x : es = [.tick,.tick,.tick,.tick,.write (L.label i) 0,.write (L.base i.val) (L.label i),
      .tick,.tick,.write (L.base i.val+1) (L.base (i.val+1)),.tick] := by
    have h := congrArg (fun v ↦ v.map Prod.fst) run
    simpa (config := {decide := true}) [-Fin.ofNat_eq_cast,putHeader,trace,Op.effect,
      BinaryOp.eval,Function.update,input.vertex,input.labels,unit,first,stride,base_index,base_next,lab] using h.symm
  rw [x]
  obtain ⟨hb,fit⟩ := base_bounds L i
  have hl : Interval L.origin L.limit (L.label i).val := by
    rw [Interval,L.label_val]; unfold WalkLayout.limit; have := i.isLt; omega
  have hf : L.limit ≤ 2^w := L.fits
  have one : (L.base i.val+1).val = (L.base i.val).val+1 := by
    rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (by omega : 1 < 2^w),Nat.mod_eq_of_lt (by omega)]
  constructor <;> intro a v h
  · simp at h
  · simp only [List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.write.injEq] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact hl
    · exact ⟨by omega,by omega⟩
    · rw [Interval,one]; exact ⟨by omega,by omega⟩

theorem append {rd wr : ℕ → Prop} {es fs : List (Event w)} (p : Reads rd es ∧ Writes wr es)
    (q : Reads rd fs ∧ Writes wr fs) : Reads rd (es++fs) ∧ Writes wr (es++fs) :=
  ⟨fun a v h ↦ (List.mem_append.mp h).elim (p.1 a v) (q.1 a v),
   fun a v h ↦ (List.mem_append.mp h).elim (p.2 a v) (q.2 a v)⟩

end CompressorRecords.Greedy.PrepareAccess

end VPVNP
end Computability
end OAI
