import OAI.Computability.BorderVNP.DiagonalTallyAllocatedReportFrame
import OAI.Computability.BorderVNP.DiagonalTallyAlignedEvaluation
import OAI.Computability.BorderVNP.DiagonalTallyReportResident

/-! # Materializer inputs after the selected cube ID suffix is appended -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCubeSuffix

open VPVNP.BurstRAM RoutingISA DiagonalTallyMaterialize DiagonalTallyRAM DiagonalTallyCellReports
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

/-- Actual source words reached by a prepared list lie below its declared exclusive bound. -/
theorem reads_below {w : ℕ} (m : Memory w) (limit p : ℕ) (os : List Operand)
    (valid : supplied m limit p os) (j : ℕ) (read : operandReads p os j) : j<limit := by
  induction os generalizing p with
  | nil => exact False.elim read
  | cons o os ih =>
    obtain ⟨hp,ho,_,_,ht⟩ := valid
    obtain ⟨off,place,digits,refs⟩ := ho
    rcases read with h | h | h | h | ⟨r,hr,eq⟩ | h
    · omega
    · simpa [h] using off
    · simpa [h] using place
    · omega
    · exact eq ▸ refs r hr
    · exact ih (p+5) ht h

/-- Concatenation of consecutive, physically validated descriptor arrays. -/
theorem supplied_append {w : ℕ} (m : Memory w) (limit p : ℕ) (xs ys : List Operand)
    (hx : supplied m limit p xs) (hy : supplied m limit (p+5*xs.length) ys) :
    supplied m limit p (xs++ys) := by
  induction xs generalizing p with
  | nil => simpa using hy
  | cons x xs ih =>
    obtain ⟨a,b,c,d,t⟩ := hx
    refine ⟨a,b,c,d,ih (p+5) t ?_⟩
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hy

/-- The one-unit operands for the actual sequence of selected table IDs. -/
def Frame.packetOperands (f : Frame) (dir trueAddr : ℕ) (ids : Fin f.count → ℕ) :=
  List.ofFn fun i => packetOperand f.parameters (f.ids+i.val) f.zeroAddr (dir+82) trueAddr (ids i)

/-- The genuine suffix write updates the total count and supplies all the cell and cube operands
together. The earlier cell descriptors and their named source words remain readable. -/
theorem Frame.supplied_after_append {w : ℕ} (f : Frame) (m mt : Memory w)
    (dir limit trueAddr : ℕ) (cells : List Operand) (ids : Fin f.count → ℕ)
    (image : readings mt=f.image dir (readings m)) (length : cells.length=f.prior)
    (old : supplied m f.start f.descriptors cells)
    (noCountRead : ∀ a, operandReads f.descriptors cells a → a≠dir+35)
    (dirRoom : dir+95<f.start) (idStart : dir+35<f.ids) (idRoom : f.ids+f.count ≤ f.start)
    (zeroRoom : f.zeroAddr<f.start) (trueRoom : trueAddr<f.start)
    (zeroFrame : f.zeroAddr≠dir+35) (trueFrame : trueAddr≠dir+35)
    (literalPtr : (m (dir+82)).val=trueAddr) (zeroValue : (m f.zeroAddr).val=0) (trueValue : (m trueAddr).val=1)
    (selected : ∀ i : Fin f.count,(m (f.ids+i.val)).val=ids i)
    (rowRoom : f.start+5*f.count ≤ limit) (coordFit : ∀ i, f.parameters+ids i<2^w)
    (wpos : 0<w) :
    supplied mt limit f.descriptors (cells++f.packetOperands dir trueAddr ids) ∧
      (mt (dir+35)).val=cells.length+(f.packetOperands dir trueAddr ids).length := by
  have old' := supplied_unchanged m mt f.descriptors f.start cells old (by
    intro j hj
    apply Fin.ext
    change readings mt j=readings m j
    rw [image,f.image_before _ _ (reads_below m f.start f.descriptors cells old j hj) (noCountRead j hj)])
  have each (i : Fin f.count) :
      (packetOperand f.parameters (f.ids+i.val) f.zeroAddr (dir+82) trueAddr (ids i)).resident mt
        (f.start+5*i.val) := by
    rw [← selected i]
    exact f.packetOperand_resident dir m mt image i.val i.isLt dirRoom idRoom zeroRoom trueAddr
      trueRoom (by omega) zeroFrame trueFrame literalPtr zeroValue trueValue
  have res := residents_ofFn mt f.start _ each
  have lim : f.start ≤ limit := by omega
  have new : supplied mt limit f.start (f.packetOperands dir trueAddr ids) := by
    apply supplied_of_residents mt f.start limit _ res (by simpa [packetOperands] using rowRoom)
    intro o ho
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho
    constructor
    · simp only [Operand.before,packetOperand,List.length_cons,List.length_nil,Nat.zero_add,
        List.mem_singleton,forall_eq]
      have hi := i.isLt
      omega
    · rw [Operand.fits,packetOperand_pair]
      refine ⟨coordFit i,wpos,?_⟩
      change 1<2^w
      exact Nat.one_lt_two_pow wpos.ne'
  refine ⟨supplied_append mt limit f.descriptors cells _ (supplied_mono mt lim _ _ old') ?_,?_⟩
  · simpa only [length,Frame.start] using new
  · change readings mt (dir+35)=_
    rw [image]
    simp [Frame.image,length,packetOperands]

end DiagonalTallyCubeSuffix

end BorderVNP
end Computability
end OAI
