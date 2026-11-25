import OAI.Optimization.LinearProgramming.Compression.SignWirePublicPorts
import OAI.Optimization.LinearProgramming.Compression.SignWireHighShell
import OAI.Optimization.LinearProgramming.Compression.SignWireCallback

/-! Public scalar-bit decoding and reply writes preserve the finite numerical
window of an arbitrary ordered field when packet storage sits beyond it. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM

theorem WireReadFrame.ports {K : Type*} {p send recv raw base : ℕ} {m t : Memory K}
    (read : WireReadFrame m t raw p) (h : PublicPorts p send recv raw base m) :
    PublicPorts p send recv raw base t :=
  h.transfer (fun i hi => read.index i (by omega) (by omega) (by omega) (by omega))

theorem ReplyWriteFrame.ports {K : Type*} {p send recv raw base : ℕ} {m t : Memory K}
    (write : ReplyWriteFrame m t) (h : PublicPorts p send recv raw base m) :
    PublicPorts p send recv raw base t :=
  h.transfer (fun i hi => write.index i (by omega) (by omega) (by omega) (by omega))

theorem WireReadFrame.highShell {K : Type*} {m t old caller : Memory K} {cap src base p : ℕ}
    (read : WireReadFrame m t src p) (far : 2*cap < src) (h : HighShell m old caller cap base p) :
    HighShell t old caller cap base p := by
  apply h.transfer
  · intro i hi hc _;exact read.data (2*i) (by omega) (Or.inl (by omega))
  · intro i hi;exact read.index (2*i) (by omega) (by omega) (by omega) (by omega)

theorem ReplyWriteFrame.highShell {K : Type*} {m t old caller : Memory K} {cap base p : ℕ}
    (write : ReplyWriteFrame m t) (far : 2*cap < m.index 47) (h : HighShell m old caller cap base p) :
    HighShell t old caller cap base p := by
  apply h.transfer
  · intro i hi hc _;exact write.data (2*i) (by omega) (by omega) (by omega)
  · intro i hi;exact write.index (2*i) (by omega) (by omega) (by omega) (by omega)

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
