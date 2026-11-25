import OAI.Computability.BorderVNP.DiagonalTallyCubeSuffix
import OAI.Computability.BorderVNP.DiagonalTallyCellOperands

/-! # Reading the physically assembled cube operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCubeSuffix

open VPVNP.BurstRAM RoutingISA DiagonalTallyPacketEmit DiagonalTallyMaterialize

/-- All source words and earlier cell descriptors outside the count update survive. -/
theorem Frame.image_before (f : Frame) (d : ℕ) (m : ℕ → ℕ) {a : ℕ}
    (ha : a<f.start) (hn : a≠d+35) : f.image d m a=m a := by
  rw [Frame.image,Function.update_of_ne hn,written_before _ _ _ ha]

/-- The actual five-word write for each vertex is readable in native memory. -/
theorem Frame.image_field (f : Frame) (d : ℕ) (m : ℕ → ℕ) (hdis : d+35<f.start)
    {i k : ℕ} (hi : i<f.count) (hk : k<5) :
    f.image d m (f.start+5*i+k) = f.field d (5*i+k) := by
  rw [Frame.image,Function.update_of_ne (by omega),Nat.add_assoc,written_at _ _ _ (by omega)]

/-- The compiled suffix reaches the genuine chosen ID and the designated true and
zero literal words at each owned vertex. -/
theorem Frame.packetOperand_resident {w : ℕ} (f : Frame) (d : ℕ) (m mt : Memory w)
    (out : readings mt=f.image d (readings m)) (i : ℕ) (hi : i<f.count)
    (hdir : d+95<f.start) (hids : f.ids+f.count≤f.start) (hz : f.zeroAddr<f.start)
    (trueAddr : ℕ) (ht : trueAddr<f.start)
    (hidframe : f.ids+i≠d+35) (hzframe : f.zeroAddr≠d+35) (htframe : trueAddr≠d+35)
    (hptr : (m (d+82)).val=trueAddr) (hzero : (m f.zeroAddr).val=0)
    (hone : (m trueAddr).val=1) :
    (packetOperand f.parameters (f.ids+i) f.zeroAddr (d+82) trueAddr (m (f.ids+i)).val).resident
      mt (f.start+5*i) := by
  have load (a : ℕ) (ha : a<f.start) (hn : a≠d+35) : (mt a).val=(m a).val := by
    change readings mt a=readings m a
    rw [out,f.image_before _ _ ha hn]
  have row (k : ℕ) (hk : k<5) :
      (mt (f.start+5*i+k)).val = f.field d (5*i+k) := by
    change readings mt (f.start+5*i+k) = _
    rw [out,f.image_field _ _ (by omega) hi hk]
  have hdr := row 0 (by decide)
  have a := row 1 (by decide)
  have b := row 2 (by decide)
  have c := row 3 (by decide)
  have e := row 4 (by decide)
  simp [Frame.field,Nat.mul_add_div (by decide : 0<5)] at hdr a b c e
  change (mt (f.start+5*i)).val=f.parameters ∧ (mt (f.start+5*i+1)).val=f.ids+i ∧
    (mt (f.ids+i)).val=(m (f.ids+i)).val ∧ (mt (f.start+5*i+2)).val=d+82 ∧
    (mt (f.start+5*i+3)).val=d+82+1 ∧ (mt (f.start+5*i+4)).val=f.zeroAddr ∧
    (mt f.zeroAddr).val=0 ∧ (mt (d+82)).val=trueAddr ∧ (mt trueAddr).val=1 ∧ True
  exact ⟨hdr,a,load (f.ids+i) (by omega) hidframe,b,c,e,(load _ hz hzframe).trans hzero,
    (load (d+82) (by omega) (by omega)).trans hptr,(load _ ht htframe).trans hone,trivial⟩

end DiagonalTallyCubeSuffix

end BorderVNP
end Computability
end OAI
