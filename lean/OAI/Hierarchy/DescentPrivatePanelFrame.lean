import OAI.Hierarchy.DescentPackedPrivateAccumulator

namespace OAI
/-! # Exact memory intervals preserved by the native private accumulator -/

namespace Hierarchy.DescentPackedPrivateAccumulator
open Computability.VPVNP.BurstRAM ProtocolRAM DescentPackedPrivateSum
variable {w H r M : ℕ}

theorem image_frame (L : Layout) (C : Counters) (grain : ℕ) (m : Memory w)
    (room : L.Room w H r M) (space : C.scaling.Room w)
    (atEnd : C.words=L.starts+Layout.count H r M) (addr : ℕ)
    (away : addr<L.words ∨ C.out<addr) :
    image L C H r M grain m addr=m addr := by
  have order:=room.sep
  have active : C.words<C.scaled:=space.active
  have temp : C.scaled<C.out:=space.temp
  rw [image,Counters.sumImage,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega),
    DescentPrivateExponentRAM.Banks.scaled,ProtocolRAMStaticPorts.frame _ _ _ _ _ (by
      change addr<C.scaled ∨ C.scaled+1≤addr
      omega)]
  rcases away with low|high
  · exact L.frame _ _ _ m _ low room
  · rw [Layout.image,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inr (by omega)),Layout.scores,
      ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (by omega))]
end Hierarchy.DescentPackedPrivateAccumulator

end OAI
