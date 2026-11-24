import OAI.Computability.VPVNP.RAMTapeAddressLogPhases

/-!
# Rewinding the private write log

A load returns the visited key bits, value bits, and occupancy markers to
three independent streams. The final pass transfers the saved result onto
the output stack. Each stream requires one empty test and two steps per bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

/-- The four final rewind passes restore the log and deliver the read result. -/
theorem restoreRuns (s : Bank) :
    StackRuns loadCode (2 * (s.sk.length + s.sv.length + s.sm.length + s.so.length) + 4)
      (.rewind .keys) s.stacks .done ({s with
        ks := s.sk.reverse ++ s.ks, vs := s.sv.reverse ++ s.vs,
        marks := s.sm.reverse ++ s.marks, o := s.so.reverse ++ s.o,
        sk := [], sv := [], sm := [], so := []} : Bank).stacks := by
  let k : Bank := {s with ks := s.sk.reverse ++ s.ks, sk := []}
  let v : Bank := {k with vs := s.sv.reverse ++ s.vs, sv := []}
  let m : Bank := {v with marks := s.sm.reverse ++ s.marks, sm := []}
  have run := (((rewindRuns .keys s).trans (rewindRuns .values k)).trans
    (rewindRuns .marks v)).trans (rewindRuns .result m)
  convert run using 1 <;> first | rfl | (dsimp [Rewind.src, Bank.stacks, k, v, m]; omega)

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI
