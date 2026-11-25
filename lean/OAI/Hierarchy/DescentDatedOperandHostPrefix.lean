import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # The original compact successor host ordinals in a larger signed arena -/
namespace Hierarchy.DescentPackedZip
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {H K G M b w : ℕ} {m : Memory w} {e : Expr} {bank : Bank} {value : Fin H → Fin G → Cell b}

theorem source_first_hosts (prefixSize : K≤H) (original : Source e value M m) :
    Source e (fun (h : Fin K) g=>value (h.castLE prefixSize) g) M m :=by
  rintro ⟨h,t⟩
  exact original (h.castLE prefixSize,t)

theorem reads_first_hosts (prefixSize : K≤H) (original : Reads bank value M m) :
    Reads bank (fun (h : Fin K) g=>value (h.castLE prefixSize) g) M m :=by
  rintro ⟨h,t⟩
  exact original (h.castLE prefixSize,t)

end Hierarchy.DescentPackedZip

end OAI
