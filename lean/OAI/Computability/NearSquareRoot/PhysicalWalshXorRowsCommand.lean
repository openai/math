import OAI.Computability.NearSquareRoot.PhysicalWalshXorNativeStage

/-! # Running an arbitrary named native matrix row in each high-prefix block -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled XorReserve NamedPacked
open CommonRegisters GeneratorSyntax Filter

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x))
    (f g : (x:X) → Input (P x) (k x) (U x))

noncomputable def windowRowsCmd (native : Cmd) :=
  let ends := rowEnds r P k hP hk u f g
  opcodeCmd ends.choose ends.choose_spec.choose native

theorem windowRowsCmd_effective {I : Type} [Primcodable I] {native : I → Cmd} (h : Effective ltr native) :
    Effective ltr (fun i => windowRowsCmd r P k hP hk u f g (native i)) := opcodeCmd_effective _ _ h

theorem windowRowsCmd_within : ∀ᶠ R : ℕ in atTop, ∀ n, Within R n → Within R (windowRowsCmd r P k hP hk u f g n) :=
  opcodeCmd_within _ _

theorem windowRowsOnNamed {native : Cmd} {l : X → ℕ} {speed : X → ℝ}
    (fits : ∀x,(u x).count ≤ l x) (row : LocalRowsAt r P k hP u f g l speed native) :
    ∃ D, WindowAt r P k u f g l speed D (windowRowsCmd r P k hP hk u f g native) := by
  let ends := rowEnds r P k hP hk u f g
  exact rowsOnNamedWith r P k hP u f g fits (e:=ends.choose_spec.choose_spec.choose)
    ends.choose_spec.choose_spec.choose_spec row

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
