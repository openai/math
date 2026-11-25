import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowsCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorOpcodeTotal

/-! # Unrestricted termination of the emitted window row command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed

/-- Run the same native command on each actual high-prefix row and collect the
new physical store. Its clock and workspace may depend on every input cell. -/
theorem windowRowsOnNamedTotal {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) (f g : (x:X) → Input (P x) (k x) (U x))
    {native : Cmd} (row : LocalRowsTotal r P k hP u f g native) :
    ∃ t s, EffectiveBoundedTask.Runs (windowRowsCmd r P k hP hk u f g native) t s
      (fun x => .fork (r.header x) (store (u x) (f x))) (fun x => store (u x) (g x)) := by
  let ends := rowEnds r P k hP hk u f g
  exact rowsOnNamedWithTotal r P k hP u f g (e:=ends.choose_spec.choose_spec.choose)
    ends.choose_spec.choose_spec.choose_spec row

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
