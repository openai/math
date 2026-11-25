import OAI.Hierarchy.DescentResetOriginalPlanes
import OAI.Hierarchy.DescentGLPackedResetFrame

namespace OAI
/-! # Running the source-field gather and basis change in the same RAM image -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D H h l c b w M N : ℕ}

set_option maxHeartbeats 1600000 in
/-- Both the matrix key and the old amount/flow words are read before the
fresh field matrix. The only installed geometry is the chosen static chart. -/
theorem gather_and_reset (C : Chart) (sizes : Size C (D*H) h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l)↪Fin N) (key : Expr)
    (L : DescentGL.Layout (h+l)) (X : Fin D→Fin H→Block (h+l)→Cell b)
    (fields : ℕ→Expr) (mem : Memory w) (fits : ∀j<D,(fields j).Fits w C.input.base)
    (ks : DescentGLControlCode.fits T key w C.input.base)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size)
    (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name mem)
    (measured : ∀i : Fin (DescentGLControlCode.Count (h+l)),key.eval mem (i.val:Word w)=((name L).val:Word w))
    (source : ∀d,DescentPackedZip.Source (fields d.val) (X d) (2^l) mem)
    (gap : C.input.base+C.input.size≤C.flags)
    (rom : ∀s : Slot (h+l),∀i : Fin C.page,mem (addr C (s,i))=literal (D*H) h l b w s i.val) :
    let n:=(schedule (h+l)).length
    let rows:=H*2^h
    let gs:=DescentPackedFlowBatch.passes C.input.base rows rows fields 0 D
    let ps:=steps (C.chosen (h+l)) (D*H) (2^h) 0 n
    let machine:=(program w gs).seq ((scan w C.flags n (T.expr key)).seq (program w ps))
    ∃out,machine.Exec mem out (clock gs+((4+n*(2*(T.expr key).work+4))+clock ps)) ∧ CheapCode machine ∧
      (∀d,Dense (h:=h) (l:=l) (slice (((C.chosen (h+l)).bank n).base) H (2^h) d)
        (fun v z=>X d v ((rearrange L).symm z)) out) ∧
      ∀a,a<C.input.base ∨ C.heap (h+l)+n*C.page≤a→ out a=mem a := by
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows fields 0 D
  let mid:=result gs mem
  have srcSize : D*(H*2^h)≤C.input.size:=by simpa only [Nat.mul_assoc] using sizes.inputSize
  have flags:=sizes.controls
  have heap:C.start≤C.heap (h+l):=Nat.le_add_right ..
  have upper:=sizes.top
  have below:C.input.base≤C.flags:=by omega
  have room:C.input.base+D*(H*2^h)<2^w:=by omega
  obtain ⟨run,loaded,low⟩:=gather_channels C.input.base fields X mem fits room source
  have gatherEnd : C.input.base + D * rows ≤ C.flags :=
    (Nat.add_le_add_left srcSize C.input.base).trans gap
  have high (a) (old : C.flags≤a) : mid a=mem a :=
    DescentPackedFlowBatch.above C.input.base rows rows fields mem 0 D a le_rfl
      (by simpa only [Nat.zero_add] using gatherEnd.trans old)
  have inst : C.install (D*H) h l b mid=mid := by
    apply stamped
    intro s i
    have hp : C.start≤addr C (s,i):=by unfold addr Chart.base;omega
    exact (high _ (by omega)).trans (rom s i)
  have ks' : DescentGLControlCode.fits T key w C.flags :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ below ks.1,
      ⟨ks.2.1.1,ks.2.1.2.1,ks.2.1.2.2.trans below⟩,
      ⟨ks.2.2.1,ks.2.2.2.1,ks.2.2.2.2.trans below⟩⟩
  have stat' : DescentGLControlCode.installed T name mid := by
    constructor
    · intro i
      exact (low _ ((Nat.add_lt_add_left (i.isLt.trans_le off) _).trans_le ks.2.1.2.2)).trans (stat.1 i)
    · intro i
      exact (low _ ((Nat.add_lt_add_left (i.isLt.trans_le area) _).trans_le ks.2.2.2.2)).trans (stat.2 i)
  have elected (i : Fin (DescentGLControlCode.Count (h+l))) :
      key.eval mid (i.val:Word w)=((name L).val:Word w) :=
    (eval_below _ _ mem mid ks.1 low).trans (measured i)
  obtain ⟨rotate,cheap,dense,frame⟩:=reset_resident C sizes T name key L (stack X) mid ks' off area stat' elected loaded gap inst
  refine ⟨_,run.then rotate,cheap_seq (ProtocolRAM.program_cheap w gs) cheap,?_,?_⟩
  · intro d
    exact slice_dense (h:=h) (l:=l) _ (fun d v z=>X d v ((rearrange L).symm z)) _ dense d
  intro a band
  rcases band with lo|hi
  · exact (frame a (.inl (lo.trans_le below))).trans (low a lo)
  · exact (frame a (.inr hi)).trans (high a (by omega))

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
