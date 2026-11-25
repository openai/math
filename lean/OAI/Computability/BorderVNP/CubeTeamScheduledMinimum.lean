import OAI.Computability.BorderVNP.CubeISAHeaderDecodeReadout
import OAI.Computability.BorderVNP.CubeTeamDeclarationReturn

/-! # The minimum check on columns materialized by the signed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA Cube.Physical VPVNP.BurstRAM

/-- Exact columns in the actual output of the declaration parser. Every summand is the
word at the matching dense-array offset, including padding zeros. -/
theorem columns_of_decoded (dyn : HeaderDecode.Layout) (l : CubeLengths.Layout) (initial : ℕ → ℕ)
    (dense : l.claimed = dyn.dense) (target : l.totals = dyn.totals) (dim : l.coordinates = dyn.a)
    (separate : dyn.dense+dyn.entries ≤ dyn.totals ∨ dyn.totals+dyn.a ≤ dyn.dense) :
    CubeLengths.ColumnsAgree l (dyn.finalImage initial) (dyn.d*dyn.d) := by
  intro j hj
  have hj' : j < dyn.a := dim ▸ hj
  rw [target,dyn.finalTotal initial hj']
  unfold CubeLengths.columnPrefix
  rw [dim,dense]
  apply Finset.sum_congr rfl
  intro k hk
  apply (dyn.finalEntry initial ?_ separate).symm
  calc k*dyn.a+j < (k+1)*dyn.a := by rw [Nat.add_mul]; omega
       _ ≤ _ := Nat.mul_le_mul_right _ (Finset.mem_range.mp hk)

/-- Every schedule return of the header decoder and the following minimum check forces
all total words and the first minimum. The native decoder writes these sums itself. -/
theorem scheduledMinimum_return {w n d : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (decl : LengthDeclaration n d) (dyn : HeaderDecode.Layout) {r : Bank w} {m : Memory w}
    {es u mu fs t mt} (decode : Runs pub mac HeaderDecode.program r m es u mu)
    (minimum : Runs pub mac CubeLengths.minimum u mu fs t mt)
    (fits : HeaderDecode.Fits dyn w) (atFrame : HeaderDecode.AtFrame dyn (readings pub) (readings m))
    (primary : readings pub 0+63 < 2^w) (header : dyn.header+12 < 2^w) (totalsRoom : dyn.totals+dyn.a ≤ 2^w)
    (separate : dyn.dense+dyn.entries ≤ dyn.totals ∨ dyn.totals+dyn.a ≤ dyn.dense)
    (sumRoom : dyn.d*dyn.d*dyn.cap < 2^w) (radix : dyn.d = d) (axes : dyn.a = n+1) :
    let l := CubeLengths.layout (readings pub) (readings mu)
    CubeLengths.Fits w (readings pub) (readings mu) → l.claimed = dyn.dense → l.totals = dyn.totals →
      l.coordinates = dyn.a → l.chosen = decl.1.val → CubeLengths.StoredRows (readings mu) l.claimed decl.2 →
      decl.1 = firstMinimum (fun j => ∑ row, decl.2 row j) ∧
        ∀ j : Fin (n+1), readings mu (l.totals+j.val) = ∑ row, decl.2 row j := by
  intro l fit dense target dim index table
  have img : readings mu = dyn.finalImage (readings m) := ((HeaderDecode.program_run dyn r m fits atFrame
    primary header totalsRoom separate sumRoom).sound decode).2
  have columns : CubeLengths.ColumnsAgree l (readings mu) (d*d) := by
    rw [img,← radix]
    exact columns_of_decoded dyn l (readings m) dense target dim separate
  have least := ((CubeLengths.minimum_run (mac := mac) u mu fit).sound minimum).1
  exact ((CubeLengths.public_iff table (dim.trans axes) index).mp ⟨columns,least⟩).symm

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
