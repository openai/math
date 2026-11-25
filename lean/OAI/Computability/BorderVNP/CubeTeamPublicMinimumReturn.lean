import OAI.Computability.BorderVNP.CubeISALengthVerified

/-! # Recovering the advertised minimum and every total from a public return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CubeLengths Cube.Physical VPVNP.BurstRAM

/-- A returned public verifier forces the advertised first minimum and the exact sum
in each physical totals cell, including when the incoming totals were untrusted. -/
theorem publicMinimum_return {w n d : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r : Bank w} {m : Memory w} {es t mt} (decl : LengthDeclaration n d)
    (run : Runs pub mac publicMinimum r m es t mt) (fit : Fits w (readings pub) (readings m))
    (shape : (layout (readings pub) (readings m)).entries = d*d*(n+1))
    (dim : (layout (readings pub) (readings m)).coordinates = n+1)
    (index : (layout (readings pub) (readings m)).chosen = decl.1.val)
    (table : StoredRows (readings m) (layout (readings pub) (readings m)).claimed decl.2) :
    decl.1 = firstMinimum (fun j => ∑ row, decl.2 row j) ∧
      ∀ j : Fin (n+1), readings m ((layout (readings pub) (readings m)).totals+j.val) = ∑ row, decl.2 row j := by
  have checked := ((publicMinimum_run (mac := mac) r m fit (d*d) (by rw [dim,shape])
    (by rw [dim]; omega)).sound run).1
  exact ((public_iff table dim index).mp checked).symm

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
