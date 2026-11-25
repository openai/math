import OAI.Computability.NearSquareRoot.PhysicalWalshXorDuskCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorGateTotal

/-! # Total execution of a specified Dusk XOR record command

The mathematical clock for a particular reached input can be enlarged to
cover both codecs, the gate call, and its return frame. None of these clocks
are values consumed by the generated physical source.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Strip Space EffectiveBoundedTask
open Controlled.PositionProgram XorSweep

noncomputable section

/-- All reached raw records terminate with the shifted read ordering.
The running-time and space bounds can vary over these actual inputs. -/
def DuskTotal {I : Type} (P L S w : I → ℕ) (header : I → Tree)
    (x : (i : I) → ℕ → Dusk.Grain (w i)) (cmd : Cmd) : Prop :=
  ∃ time space : I → ℕ, EffectiveBoundedTask.Runs cmd time space
    (fun i => .fork (duskHeader (header i) (2^(P i+3*L i)) (S i) (w i))
      (send ((List.range (2^(P i+3*L i)*S i)).map (Dusk.mark ∘ x i))))
    (fun i => send ((List.range (2^(P i+3*L i)*S i)).map
      (Dusk.mark ∘ x i ∘ directedRead (L i) (S i))))

/-- Wrap exactly the same gate program that the cost-sensitive Dusk compiler
uses, from its uncharged execution on the selected inputs. -/
theorem duskOfTotalNamed {I : Type} (P L S w : I → ℕ) (hs : ∀ i, 0 < S i)
    (header : I → Tree) (x : (i : I) → ℕ → Dusk.Grain (w i)) {c : Cmd}
    (inner : ∃ time space : I → ℕ, EffectiveBoundedTask.Runs c time space
      (fun i => .fork (header i) (store (Series.natural (S i*(2*(w i+1)))) (duskRow (P:=P i) (L:=L i) (x i))))
      (fun i => store (Series.natural (S i*(2*(w i+1))))
        (duskRow (P:=P i) (L:=L i) (x i) ∘ directed (gate (L i))))) :
    DuskTotal P L S w header x (duskCmd c) := by
  obtain ⟨time,space,core⟩ := inner
  let io i := (2^(P i+3*L i)*S i+1)*(w i+1)
  let area i := max (io i) (space i)
  let full i := max (time i) (area i)
  exact ⟨full,area,duskOfGateNamed P L S w hs header full area (fun _ => le_max_right ..) x
    (fun _ => le_max_left ..) (core.mono (fun _ => le_max_left ..) (fun _ => le_max_right ..))⟩

/-- Select a reached descriptor and its actual payload from the gate's
unrestricted indexed correctness certificate. -/
theorem duskOfGateTotal {X Y : Type} (r : Regime X) (P L S w : X → ℕ) {c : Cmd}
    (core : GateTotal r P (fun x => 3*L x) (fun x => Series.natural (S x*(2*(w x+1)))) c)
    (select : Y → X) (hs : ∀ y, 0 < S (select y))
    (x : (y : Y) → ℕ → Dusk.Grain (w (select y))) :
    DuskTotal (P ∘ select) (L ∘ select) (S ∘ select) (w ∘ select) (r.header ∘ select) x (duskCmd c) := by
  obtain ⟨time,space,run⟩ := core
  let pick (y : Y) : (b : X) × Input (P b) (3*L b) (Fin (S b*(2*(w b+1)))) :=
    ⟨select y,duskRow (P := P (select y)) (L := L (select y)) (x y)⟩
  apply duskOfTotalNamed _ _ _ _ hs _ x
  refine ⟨time ∘ pick,space ∘ pick,?_⟩
  simpa only [pick,Function.comp_def,Nat.mul_div_cancel_left _ (by decide : 0 < 3)] using run.on pick

end
end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
