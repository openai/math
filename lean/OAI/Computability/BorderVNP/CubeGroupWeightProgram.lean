import OAI.Computability.BorderVNP.CubeGroupWeightFrame
import OAI.Computability.BorderVNP.CubeGroupWeightPass

/-! # Native sparse assembly of the actual team-weight vector -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- All three histogram passes start from the ordinary allocated input frame. -/
def program : Code := .block [setup,Phase.init.scan,Phase.shared.scan,Phase.data.scan]

/-- Each group, ordered declaration pair and packed cell is visited once. -/
def ticks (l : Layout) := setup.slots + (Phase.init.ticks l + (Phase.shared.ticks l + Phase.data.ticks l))

/-- Complete output in the physical frame-75 interval. -/
structure Result (l : Layout) (orig mem : ℕ → ℕ) : Prop where
  /-- Each public group has its exact rational charge in millionths of a word. -/
  weights : ∀ s < l.groups, mem (l.weights+s) = l.weight orig s
  /-- Every other physical word survives the histogram program. -/
  outside : ∀ a, (∀ s < l.groups, a ≠ l.weights+s) → mem a = orig a

/-- From actual declared lengths, cell labels and receiving data words, the finite
program computes each weight exactly, preserving every other memory address. -/
theorem run_program {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (hf : readings pub 0 = l.frame)
    (fields : l.Fields (readings m)) (room : l.SetupRoom w) (fit : l.Fits w (readings m)) :
    BoundedRun pub macros program s m (ticks l) (fun z => Result l (readings m) z.mem) := by
  apply (run_setup pub macros l s m fields room hf).seq
  rintro u mu ⟨hr,hm⟩
  change readings mu = readings m at hm
  have initial : Image .init l (readings m) (readings mu) 0 := by
    rw [hm]
    exact ⟨fun _ _ => by simp [Phase.value], fun _ _ => rfl⟩
  apply (Phase.init.run_scan pub macros l _ u mu fit hr initial).seq
  rintro v mv ⟨hr',ht⟩
  have shared : Image .shared l (readings m) (readings mv) 0 := by
    refine ⟨fun k hk => ?_, ht.outside⟩
    have hv := ht.weights k hk
    simpa [Phase.value,Phase.count,hk,NatState.ofWords,Layout.sharedTotal,TeamNative.scaledWeight] using hv
  apply (Phase.shared.run_scan pub macros l _ v mv fit hr' shared).seq
  rintro u' mu' ⟨hr'',hs⟩
  have data : Image .data l (readings m) (readings mu') 0 := by
    refine ⟨fun k hk => ?_, hs.outside⟩
    simpa [Phase.value,Phase.count,NatState.ofWords,Layout.dataTotal] using hs.weights k hk
  apply (Phase.data.run_scan pub macros l _ u' mu' fit hr'' data).mono le_rfl
  exact fun _ h => ⟨h.2.weights,h.2.outside⟩

/-- Deterministic public bytecode suffices for all three passes. -/
theorem program_deterministic : program.deterministic = true := by decide

/-- A constant setup, a linear scan of cells and a quadratic scan of the symbol
alphabet give the tick bound. -/
theorem ticks_le (l : Layout) :
    ticks l ≤ setup.slots + 32*(l.groups*l.groups+l.cells+l.groups)+6 := by
  change setup.slots + (l.groups*(Phase.init.body.slots+1)+2 +
    (l.groups*l.groups*(Phase.shared.body.slots+1)+2 + (l.cells*(Phase.data.body.slots+1)+2))) ≤ _
  have h0 : Phase.init.body.slots+1 ≤ 32 := by decide
  have h1 : Phase.shared.body.slots+1 ≤ 32 := by decide
  have h2 : Phase.data.body.slots+1 ≤ 32 := by decide
  have b0 := Nat.mul_le_mul_left l.groups h0
  have b1 := Nat.mul_le_mul_left (l.groups*l.groups) h1
  have b2 := Nat.mul_le_mul_left l.cells h2
  rw [show 32*(l.groups*l.groups+l.cells+l.groups) = (l.groups*l.groups)*32+l.cells*32+l.groups*32 by ring]
  omega

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
