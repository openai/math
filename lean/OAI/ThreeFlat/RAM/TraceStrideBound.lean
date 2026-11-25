import OAI.ThreeFlat.Diagonal.TraceSourceDigits
import OAI.ThreeFlat.Diagonal.TraceRecordWord

namespace OAI
/-! # The local hidden reservation fits the physical trace port budget -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Diagonal.TraceSourceOwner

theorem stride_le_ports (w p r k S f d gates : ℕ) :
    (shape w p r k S f d gates).stride ≤ 2*Diagonal.TraceAddressRecord.portRowWords w p r k d + gates := by
  unfold Shape.stride Shape.track shape Diagonal.TraceAddressRecord.portRowWords
  ring_nf
  omega

end ThreeFlat.RAM.TraceBucketAtom

end OAI
