import OAI.Computability.NearSquareRoot.InterchangeROMStageVolumeBounds
import OAI.Computability.NearSquareRoot.InterchangeROMStageComplete

/-! # End-to-end stage resource bounds on the native payload trajectory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageVolume
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip Space
  InterchangeROM InterchangeROMStage InterchangeROMStage.Frame.Realization InterchangeROMStageTable

variable {A Y : Type} (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime]
  (addr : Series A) (payload : Series Y) (π : r.NativeMove → Equiv.Perm (A × Y))
  (data : Fin (Frame.labels c.1) → A × Y → Fin c.2.2.1 → ZMod c.2.1)

/-- The live tree at every boundary fits the same schedule-dependent envelope. -/
theorem runState_size (header : Tree) (n : ℕ) :
    (runState c r addr payload π data header n).count+1 ≤
      packetFactor c*mass header addr.count payload.count :=
  uniform_typed c r n addr (fun _ => payload) payload.count (fun _ => le_rfl)
    (fun a i z d => stages c r π data n z (a,i) d) header

/-- Only the recursive movement calls contribute to the additional time and
peak allowances. All local bank sizes and matrix scans are paid by effective
functions of the serialized stage and the live input mass. -/
theorem native (header : Tree) (S D : ℕ) (charts : List Opcode.Word) (wordCmd : Opcode.Word → Cmd)
    (env : Env) (rowsTime : (k : Fin 6) → r.Boundary (routePos k+1) × Fin c.2.2.1 → ℕ)
    (active : ∀ k : Fin 5, 0 < (c.1.bank (inputBoundary k)).length*c.2.2.1)
    (movement : ∀ (k : Fin 6) (z : r.Boundary (routePos k+1)) (d : Fin c.2.2.1) deck b,
      DeckCap b deck → BoundedFits env (wordCmd (lookup charts (r.operand (r.moveAt k z))))
        (pile 0 (.fork header (runRow c r addr payload π data (routePos k) (r.srcAt k z) d)) deck)
        (pile 0 (runRow c r addr payload π data (routePos k+1) z d) deck)
        (rowsTime k (z,d)) (b+S) D)
    (deck : Deck) (b : ℕ) (hb : DeckCap b deck) :
    let m := mass header addr.count payload.count
    BoundedFits env (rawStage c.1 c.2.1 c.2.2.1 (gateMatrix c) charts wordCmd)
      (pile 0 (runState c r addr payload π data header 0) deck)
      (pile 0 (runState c r addr payload π data header 11) deck)
      (stageFactor c*m + ∑ k, costSum (rowsTime k) (r.cells (routePos k+1) c.2.2.1))
      (b+(localFactor c*m+S)) (localFactor c*m+D+1) := by
  let m := mass header addr.count payload.count
  let V := packetFactor c*m - 1
  let B := localFactor c*m
  let T := B-V
  have hm : 1 ≤ m := by dsimp [m,mass]; omega
  have bound (n : ℕ) := runState_size c r addr payload π data header n
  have vol (n : ℕ) : (runState c r addr payload π data header n).count ≤ V := by
    have h := bound n
    change _ ≤ packetFactor c*m at h
    dsimp only [V]
    omega
  have plus : V+1 ≤ packetFactor c*m := by
    have h := bound 0
    change _ ≤ packetFactor c*m at h
    dsimp only [V]
    omega
  have v0 := Nat.le_of_succ_le plus
  have rt (k : Fin 6) := route_local c (routePos k) V V m plus v0
  have space : 170*(V+1)+V ≤ B := (rt 0).2
  have vmax : V ≤ B := by omega
  have gt (k : Fin 5) : gateClock c header.count addr.count payload.count k ≤ T := by
    have h := (gate_local c k header addr.count payload.count V v0).2
    change V+gateClock c header.count addr.count payload.count k ≤ B at h
    dsimp only [T]
    omega
  have result := InterchangeROMStage.run c r addr payload π data header V T S D charts wordCmd env rowsTime active
    (fun n _ => vol n) gt movement deck b hb
  let ledger (k : Fin 6) := costSum (rowsTime k) (r.cells (routePos k+1) c.2.2.1)
  have tt (k : Fin 5) : gateClock c header.count addr.count payload.count k ≤ B :=
    (gt k).trans (Nat.sub_le ..)
  have tm := clock c m hm (fun k => routeClock c V k+ledger k) ledger
    (gateClock c header.count addr.count payload.count)
    (fun k => Nat.add_le_add_right (rt k).1 _) tt
  apply result.mono tm
  · change b+max (V+T) (170*(V+1)+V+S) ≤ b+(B+S)
    dsimp only [T]; omega
  · change max T (170*(V+1)+D)+1 ≤ B+D+1
    dsimp only [T]; omega

end InterchangeROMStageVolume

end NearSquareRoot
end Computability
end OAI
