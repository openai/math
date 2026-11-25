import OAI.Computability.NearSquareRoot.InterchangeROMStageTape

/-! # End-to-end execution of the grouped interchange stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMStage

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM InterchangeROMStageTable InterchangeROMTable Frame.Realization Space

variable {A Y : Type} (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime]
  (addr : Series A) (payload : Series Y) (π : r.NativeMove → Equiv.Perm (A × Y))
  (data : Fin (Frame.labels c.1) → A × Y → Fin c.2.2.1 → ZMod c.2.1)

abbrev stages (n : ℕ) :=
  r.states c.2.1 c.2.2.1 (decode c).minor (decode c).base (decode c).query π data n

/-- A scalar ground-field row with all payload entries aligned at each address. -/
def runRow (n : ℕ) (z : r.Boundary n) (d : Fin c.2.2.1) : Tree :=
  stripe addr fun a => stripe payload fun i => numeral (stages c r π data n z (a,i) d).val

/-- The exact invariant on register zero, including the parent header. -/
def runState (header : Tree) (n : ℕ) : Tree :=
  .fork header (r.Tape n c.2.2.1 (runRow c r addr payload π data n))

def gateClock (c : Parameters) (H N w : ℕ) (k : Fin 5) :=
  84*H+charge c (c.1.gate k (inputBoundary k)) N w+11

def routeClock (c : Parameters) (V : ℕ) (k : Fin 6) :=
  ((c.1.bank (routePos k+1)).length*c.2.2.1+2)*(160*(V+1))

/-- One actual P192 program performs all eleven operators of the typed paper stage.
The recursive movement clocks occur once per scalar row. -/
theorem run (header : Tree) (V T S D : ℕ) (charts : List Opcode.Word) (wordCmd : Opcode.Word → Cmd)
    (env : Env) (rowsTime : (k : Fin 6) → r.Boundary (routePos k+1) × Fin c.2.2.1 → ℕ)
    (active : ∀ k : Fin 5, 0 < (c.1.bank (inputBoundary k)).length*c.2.2.1)
    (volume : ∀ n ≤ 11, (runState c r addr payload π data header n).count ≤ V)
    (localTime : ∀ k, gateClock c header.count addr.count payload.count k ≤ T)
    (movement : ∀ (k : Fin 6) (z : r.Boundary (routePos k+1)) (d : Fin c.2.2.1) deck b,
      DeckCap b deck → BoundedFits env (wordCmd (lookup charts (r.operand (r.moveAt k z))))
        (pile 0 (.fork header (runRow c r addr payload π data (routePos k) (r.srcAt k z) d)) deck)
        (pile 0 (runRow c r addr payload π data (routePos k+1) z d) deck)
        (rowsTime k (z,d)) (b+S) D)
    (deck : Deck) (b : ℕ) (hb : DeckCap b deck) :
    BoundedFits env (rawStage c.1 c.2.1 c.2.2.1 (gateMatrix c) charts wordCmd)
      (pile 0 (runState c r addr payload π data header 0) deck)
      (pile 0 (runState c r addr payload π data header 11) deck)
      (23 + (∑ k : Fin 6, (routeClock c V k + costSum (rowsTime k) (r.cells (routePos k+1) c.2.2.1))) +
        ∑ k, gateClock c header.count addr.count payload.count k)
      (b+max (V+T) (170*(V+1)+V+S)) (max T (170*(V+1)+D)+1) := by
  let tape := runState c r addr payload π data header
  refine join_rawStage c charts wordCmd tape
    (fun k => routeClock c V k + costSum (rowsTime k) (r.cells (routePos k+1) c.2.2.1))
    (gateClock c header.count addr.count payload.count) (max (V+T) (170*(V+1)+V+S))
    (max T (170*(V+1)+D)) env ?_ ?_ ?_ deck b hb
  · exact (volume 11 le_rfl).trans ((Nat.le_add_right _ _).trans (le_max_left ..))
  · intro k deck b live
    let n := routePos k
    have hn : n+1 ≤ 11 := by fin_cases k <;> decide
    have s₁ := volume n (by omega)
    have s₂ := volume (n+1) hn
    have h := r.execute_route_typed (r.correctRoute_at k) (fun v => wordCmd (lookup charts v)) header
      (runRow c r addr payload π data n) (runRow c r addr payload π data (n+1)) (rowsTime k) S D env
      (movement k) deck b live
    apply h.mono
    · apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 160 (Nat.succ_le_succ s₁))
    · change b+170*((tape n).count+1)+(tape (n+1)).count+S ≤ _
      change (tape n).count ≤ V at s₁
      change (tape (n+1)).count ≤ V at s₂
      omega
    · change 170*((tape n).count+1)+D ≤ _
      change (tape n).count ≤ V at s₁
      omega
  · intro k deck b live
    let n := inputBoundary k
    let : Fintype (r.Boundary n) :=
      Fintype.ofEquiv (Fin (c.1.bank n).length) (r.indexEquiv n).symm
    let input := fun a (i : Y) (z : r.Boundary n) d => stages c r π data n z (a,i) d
    have h := raw_gate_typed c r k addr (fun _ => payload) payload.count (fun _ => le_rfl)
      (active k) input header env deck b live
    have y (a : A) (i : Y) (z : r.Boundary (n+1)) :
        gateNative r c.2.1 c.2.2.1 (decode c).minor (decode c).base (decode c).query k
          (input a i) z = stages c r π data (n+1) z (a,i) :=
      (r.states_gate _ _ _ _ _ π data k z (a,i)).symm
    simp only [y] at h
    have vk := volume n (by fin_cases k <;> decide)
    have tk := localTime k
    change BoundedFits env _ (pile 0 (tape n) deck) (pile 0 (tape (n+1)) deck) _
      (b+((tape n).count+gateClock c header.count addr.count payload.count k)) _ at h
    apply h.mono le_rfl _ (tk.trans (le_max_left ..))
    exact Nat.add_le_add_left ((Nat.add_le_add vk tk).trans (le_max_left ..)) _

end InterchangeROMStage

end

end NearSquareRoot
end Computability
end OAI
