import OAI.ThreeFlat.RAM.FixedTraceProgram
import OAI.ThreeFlat.RAM.PhysicalScanFrame
import OAI.ThreeFlat.RAM.PhysicalTraceRows

namespace OAI
/-! # Native construction of the eleven-word X records read by the H program -/

namespace ThreeFlat.RAM.PhysicalTraceSource

open Computability.VPVNP.BurstRAM PrivateRAM BitLayout DescriptorScan Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [CommSemiring F] {w q t b p P R : ℕ}

/-- Denotation of the fixed ROM word at an arbitrary address of the whole X image. -/
theorem row_correct (G : BitNetwork F q) (code : FieldCode F w) (keys : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (base gateBase portBase : ℕ)
    (data : Fin FixedTraceProgram.P → Word w) (m₀ : Memory w)
    (pub : ∀ i, data (FixedTraceProgram.extra i)=
      FixedTraceProgram.publicWords G code p b base gateBase portBase i)
    (gate : ∀ (i : Fin G.cells) (j : Fin 11),m₀ (gateBase+11*i.val+j.val)=record G code i j)
    (fields : ∀ (j : Fin q) z,m₀ (TraceAddressReader.address portBase j.val z)=
      (TraceAddressReader.fields (keys j) z : Word w))
    (gateSep : base+11*(expanded G input).cells ≤ gateBase)
    (portSep : base+11*(expanded G input).cells ≤ portBase)
    (_destFit : base+11*(expanded G input).cells < 2^w)
    (gateFit : gateBase+11*G.cells ≤ 2^w) (portFit : portBase+11*q ≤ 2^w)
    (safe : ∀ (v : Fin t) j,(keys j).Fits w v.val)
    (addr : ∀ (v : Fin t) j,(keys j).eval v.val=sourceAddress (input v j))
    (sourceFit : 2+q+G.internal<2^w) (widthFit : G.cells<2^w) (eleven : 11<2^w) :
    ∀ (a : Word w) (m : Memory w), base≤a.val → a.val<base+11*(expanded G input).cells →
      agreesOutside base (base+11*(expanded G input).cells) m m₀ →
      (FixedTraceProgram.program w).eval data m (fun _ => a)=rowWord (expanded G input) code base a.val := by
  let X := expanded G input
  intro a m lo hi keep
  obtain ⟨⟨cell,slot⟩,eq⟩ := BitNetwork.exists_rowLocation (q:=X.cells) lo hi
  let j : Fin 11 := finSumFinEquiv slot
  obtain ⟨⟨v,u⟩,hc⟩ :=
    (finProdFinEquiv (m:=t) (n:=G.cells)).surjective cell
  let n := GuardedDescriptor.recordAddress base G.cells 0 v.val u.val j.val
  have hn : n=a.val := by
    rw [← eq,← hc]
    change base+(11*(v.val*(G.cells+0)+u.val)+j.val) =
      base+11*(u.val+G.cells*v.val)+j.val
    rw [Nat.add_zero]
    ac_rfl
  have hg (i : Fin G.cells) (z : Fin 11) : m (gateBase+11*i.val+z.val) = record G code i z :=
    (keep _ (Or.inr (by omega))).trans (gate i z)
  have hp (i : Fin q) (z : Fin 11) : m (TraceAddressReader.address portBase i.val z) =
      (TraceAddressReader.fields (keys i) z : Word w) :=
    (keep _ (Or.inr (by unfold TraceAddressReader.address; omega))).trans (fields i z)
  have h := FixedTraceProgram.row G code keys input base gateBase portBase data m
    pub hg hp gateFit portFit safe addr sourceFit widthFit eleven v u j (by change n < 2^w; rw [hn]; exact a.isLt)
  change (FixedTraceProgram.program w).eval _ _ (fun _ => (n : Word w)) = _ at h
  have cast : (n : Word w)=a := by rw [hn]; exact Fin.cast_val_eq_self a
  rw [cast,hc] at h
  rw [h,← eq]
  exact (rowWord_at X code base cell j).symm

/-- Once the small local gate and port tables have been packed above the
destination, the fixed 430-bind ROM materializes every physical X word. -/
theorem generate (G : BitNetwork F q) (code : FieldCode F w) (keys : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (base gateBase portBase : ℕ)
    (A : PhysicalScan.Frame (FixedTraceProgram.program w) P R)
    (M : Machine w P R FixedTraceProgram.P) (c : Config w P R) (m₀ : Memory w)
    (rom : ∀ j,M.code (A.pc j)=A.emit base (base+11*(expanded G input).cells) j)
    (start : c.pc=A.drv 0)
    (pub : ∀ i, M.publicData (FixedTraceProgram.extra i)=
      FixedTraceProgram.publicWords G code p b base gateBase portBase i)
    (gate : ∀ (i : Fin G.cells) (j : Fin 11),m₀ (gateBase+11*i.val+j.val)=record G code i j)
    (fields : ∀ (j : Fin q) z,m₀ (TraceAddressReader.address portBase j.val z)=
      (TraceAddressReader.fields (keys j) z : Word w))
    (gateSep : base+11*(expanded G input).cells ≤ gateBase)
    (portSep : base+11*(expanded G input).cells ≤ portBase)
    (destFit : base+11*(expanded G input).cells < 2^w)
    (gateFit : gateBase+11*G.cells ≤ 2^w) (portFit : portBase+11*q ≤ 2^w)
    (safe : ∀ (v : Fin t) j,(keys j).Fits w v.val)
    (addr : ∀ (v : Fin t) j,(keys j).eval v.val=sourceAddress (input v j))
    (sourceFit : 2+q+G.internal<2^w) (widthFit : G.cells<2^w) (eleven : 11<2^w) :
    ∃ steps ≤ 4+11*(expanded G input).cells*864, ∃ out : Config w P R, out.pc=A.exit ∧
      advance M.program steps c m₀ = some (out,fillSegment base (11*(expanded G input).cells)
        (rowWord (expanded G input) code base) m₀) := by
  obtain ⟨steps,bound,out,done,run⟩ := A.advance M base (11*(expanded G input).cells) destFit rom c m₀ start
    (rowWord (expanded G input) code base) (row_correct G code keys input base gateBase portBase
      M.publicData m₀ pub gate fields gateSep portSep destFit gateFit portFit safe addr sourceFit widthFit eleven)
  refine ⟨steps,bound.trans ?_,out,done,run⟩
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have h := FixedTraceProgram.size w
  omega

end ThreeFlat.RAM.PhysicalTraceSource

end OAI
