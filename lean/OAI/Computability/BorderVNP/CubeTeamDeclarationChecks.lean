import OAI.Computability.BorderVNP.CubeISALocalRowChecked
import OAI.Computability.BorderVNP.CubeTeamOwnedGroups
import OAI.Computability.BorderVNP.CubeTeamRowVisitAt
import OAI.Computability.BorderVNP.CubeTeamRowCoverage

/-! # Declaration entries forced by actual returning owned-role visits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.LocalRow RoutingISA.CellDispatch Cube.Physical Cube.Physical.Owned Cube.Tally VPVNP.BurstRAM

/-- Addresses of the table, subtotal workspace, and selector bank on the team that checks the row. -/
structure CheckAddresses where
  /-- Base of the powers of the alphabet size. -/
  powers : ℕ
  /-- Secondary header. -/
  header : ℕ
  /-- Physical selector and packet bank. -/
  bank : ℕ
  /-- Temporary row of recomputed subtotals. -/
  actual : ℕ
  /-- Dense table of advertised coordinate counts. -/
  claimed : ℕ

/-- The frame operands read by the strict and diagonal role programs. -/
def CheckAddresses.layout (v : CheckAddresses) (d blocks b h : ℕ) : OwnedRowSetup.Layout :=
  ⟨d,blocks,h*b,v.powers,v.header,v.bank⟩

/-- Concrete metadata and word values at the checker entry, after the scatter. The table
contains the received declaration. The subtotal area may initially contain arbitrary words. -/
structure CheckWords {n d w : ℕ} (blocks b h K s : ℕ) (v : CheckAddresses) (pub : Arg → Word w)
    (decl : LengthDeclaration n d) (x y : Fin d) (r : Bank w) (m : Memory w) : Prop where
  /-- Frame operands and addressable powers. -/
  loaded : (v.layout d blocks b h).Loaded n (readings pub) (readings m)
  /-- Actual-row pointer. -/
  actual : readings m v.header = v.actual
  /-- Claimed-row pointer. -/
  claimed : readings m (v.header+1) = v.claimed
  /-- All claimed table words came from the declaration. -/
  table : CubeLengths.StoredRows (readings m) v.claimed decl.2
  /-- The concrete scratch and table intervals fit and have the required order. -/
  space : Space (v.layout d blocks b h) w n b h K s (readings pub 0) v.actual v.claimed
  /-- Registers carry the decoded coordinate and the actual two grouping symbols. -/
  entry : OwnedStages.Entry decl.1 x y r

/-- The second program of a genuine strict-side return validates the declared counts of its
row against the actual selector fields surviving the scatter. -/
theorem strictRole_counts {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (decl : LengthDeclaration n d) (select : Packet n d blocks → Selector n K h) (pair : Symbols d)
    {r m es t mt} (run : Runs pub mac (strictRole n b h K s) r m es t mt)
    (inputs : ∀ {gs u mu}, Runs pub mac (OwnedStages.strictSide n b h K s) r m gs u mu →
      ∃ v : CheckAddresses, CheckWords blocks b h K s v pub decl pair.val.1 pair.val.2 u mu ∧
        ∀ p : {p : Packet n d blocks // p.1.1 decl.1 = pair}, SelectorRead.Stored (readings mu)
          (v.bank+packetIndex p.val*bankWidth n b h K s) (select p.val))
    (labels : d^(n+1) ≤ 2^w) (packets : packetTrials n d blocks*(h*s) < 2^w)
    (cap : declarationCap n d blocks b h s < 2^w) :
    ∀ j, decl.2 (Sym2.mk pair.val.1 pair.val.2) j = subtotals itemRow (crossCount b s select) decl.1
      (Sym2.mk pair.val.1 pair.val.2) j := by
  obtain ⟨_,u,mu,_,_,scatter,checked⟩ := seq_split run
  obtain ⟨v,z,stored⟩ := inputs scatter
  have ok := ((strictChecked_run pub mac u mu (v.layout d blocks b h) decl.1 pair b h K s
    v.actual v.claimed select decl.2 z.loaded z.actual z.claimed z.table z.space rfl labels packets cap
    stored z.entry.zero z.entry.one z.entry.axis z.entry.left z.entry.right).sound checked).1
  exact fun j => (ok j).symm

/-- The repeated-symbol role validates its one complete singleton orientation. -/
theorem diagonalRole_counts {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (decl : LengthDeclaration n d) (select : Packet n d blocks → Selector n K h) (x : Fin d)
    {r m es t mt} (run : Runs pub mac (diagonalRole n b h K s) r m es t mt)
    (inputs : ∀ {gs u mu}, Runs pub mac (OwnedStages.diagonalSide n) r m gs u mu →
      ∃ v : CheckAddresses, CheckWords blocks b h K s v pub decl x x u mu)
    (labels : d^(n+1) ≤ 2^w) (cap : declarationCap n d blocks b h s < 2^w) :
    ∀ j, decl.2 (Sym2.mk x x) j = subtotals itemRow (crossCount b s select) decl.1 (Sym2.mk x x) j := by
  obtain ⟨_,u,mu,_,_,scatter,checked⟩ := seq_split run
  obtain ⟨v,z⟩ := inputs scatter
  have ok := ((diagonalChecked_run pub mac u mu (v.layout d blocks b h) decl.1 x b h K s
    v.actual v.claimed select decl.2 z.loaded z.actual z.claimed z.table z.space rfl labels cap
    z.entry.zero z.entry.one z.entry.axis z.entry.left z.entry.right).sound checked).1
  exact fun j => (ok j).symm

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
