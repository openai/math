import OAI.Computability.BorderVNP.CubeISALocalRowRole
import OAI.Computability.BorderVNP.CubeISALocalRowStrict
import OAI.Computability.BorderVNP.CubeISALocalRowDiagonal

/-! # Exact native verification of the physical declaration at every owned row

The declaration comes from the parsed common header. The packet selector
fields come from the preceding strict-side assembly. The native role reads
both, resets its subtotal on every incidence, checks each coordinate, and
preserves all shared inputs and outer cursors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally CubeLengths OwnedRowSetup

variable {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- Actual per-strict-role allowance, including the coordinate-row zero fill and comparison. -/
def strictTicks {d : ℕ} (n b h K s blocks : ℕ) (i : Fin (n+1)) (pair : Symbols d) : ℕ :=
  (setup n b h K s).slots+(4*(n+1)+1+
    (DeclaredRow.strictCost i pair blocks b K h+(3+(5+((n+1)*(rowBody.slots+1)+1)))))

/-- Actual per-diagonal-role allowance, including its single scalar orientation. -/
def diagonalTicks {d : ℕ} (n b h K s blocks : ℕ) (i : Fin (n+1)) (a : Fin d) : ℕ :=
  (setup n b h K s).slots+(4*(n+1)+1+
    ((4+SingleTally.rowCost i a a (blocks*(h*b)))+(5+((n+1)*(rowBody.slots+1)+1))))

private theorem claimProtected {l : OwnedRowSetup.Layout} {b h K s frame actual claimed : ℕ}
    (space : Space l w n b h K s frame actual claimed) (lo hi : Fin l.d) (j : Fin (n+1)) :
    Protected n h actual (head l n b h K s) (atPair claimed l.d n lo.val hi.val+j.val) := by
  have lim := row_before_bank space lo hi
  have bank := bank_le_head l n b h K s
  have hi := j.isLt
  exact ⟨(claimOutside space lo _ j).1,.inl (by omega)⟩

/-- A complete strict role accepts precisely its correct coordinate vector, for
the actual packet selector tuple and the decoded public table. No row totals are
assumed in the mutable scratch. -/
theorem strictChecked_run (r : Bank w) (m : Memory w) (l : OwnedRowSetup.Layout) (i : Fin (n+1)) (pair : Symbols l.d)
    (b h K s actual claimed : ℕ) (select : Packet n l.d l.blocks → Selector n K h)
    (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (A : readings m l.header = actual)
    (D : readings m (l.header+1) = claimed) (table : StoredRows (readings m) claimed rows)
    (space : Space l w n b h K s (readings pub 0) actual claimed) (bc : l.bc = h*b)
    (labelFit : l.d^(n+1) ≤ 2^w) (packetFit : packetTrials n l.d l.blocks*(h*s) < 2^w)
    (capFit : declarationCap n l.d l.blocks b h s < 2^w)
    (stored : ∀ p : {p : Packet n l.d l.blocks // p.1.1 i = pair},
      SelectorRead.Stored (readings m) (l.bank+packetIndex p.val*bankWidth n b h K s) (select p.val))
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (left : readings r 14 = pair.val.1.val) (right : readings r 15 = pair.val.2.val) :
    let row := Sym2.mk pair.val.1 pair.val.2
    let values := subtotals itemRow (crossCount b s select) i row
    TestRun pub mac (strictChecked n b h K s) r m (strictTicks n b h K s l.blocks i pair)
      (∀ j, values j = rows row j)
      (Return h actual (head l n b h K s) (readings r) (readings m) values) := by
  intro row values
  let hd := head l n b h K s
  let claim := atPair claimed l.d n pair.val.1.val pair.val.2.val
  have lim := row_before_bank space pair.val.1 pair.val.2
  have bank := bank_le_head l n b h K s
  have ca := space.beforeClaim
  have cb := space.beforeBank
  have endRoom := space.endRoom
  apply role_run pub mac r m l i pair.val.1 pair.val.2 b h K s actual claimed _ _ _ values
    loaded A D space h0 h1 axis left right (strictChecked_keeps n b h K s)
  intro t mt clearState same
  have cfg := clearState.cfg
  rw [bc] at cfg
  have h8 : readings t 8 = hd := clearState.descriptor
  have packet : Owned.packetReady (blocks := l.blocks) i pair (bankWidth n b h K s) l.bank 0 (.ofWords t mt) :=
    clearState.packet pair.property
  have room : PacketTally.Rooms w n l.d l.blocks K h actual (hd+8) (readings t 8) l.bank (bankWidth n b h K s) :=
    by rw [h8]; exact packetRooms space
  have header : PacketTally.Header (readings mt) (readings t 8) n K h actual (hd+8) s := by rw [h8]; exact clearState.header
  have words (j : Fin (n+1)) : readings mt (claim+j.val) = rows row j :=
    (same _ (claimProtected space _ _ j)).trans (atPair_stored table _ _ pair.property.le j)
  have store (p : {p : Packet n l.d l.blocks // p.1.1 i = pair}) :
      SelectorRead.Stored (readings mt) (l.bank+packetIndex p.val*bankWidth n b h K s) (select p.val) := by
    intro j
    have inter := packetWord_between (b := b) (s := s) p.val j
    exact (same _ ⟨.inr (by omega),.inl inter.2⟩).trans (stored p j)
  apply (strictTail_run pub mac t mt i pair b s actual (hd+8) l.bank (bankWidth n b h K s) claim
    (readings r 7) select (rows row) packet cfg header room space.frameFit.endpoints labelFit space.dimension
    packetFit store (fun j => (subtotal_le_cap select i j row).trans_lt capFit) clearState.zeros
    clearState.declared clearState.saved words (claimOutside space _ _) (by dsimp only [claim]; omega)).mono le_rfl Iff.rfl
  rintro z ⟨v,rr,out⟩
  refine ⟨v,rr,fun x hx => out x ⟨hx.1,?_⟩⟩
  rcases hx.2 with a|a
  · exact .inl (by dsimp only [hd]; omega)
  · exact .inr a

/-- The diagonal role checks one scalar orientation against its actual public
row, with exactly the same per-incidence scratch reset and restored cursors. -/
theorem diagonalChecked_run (r : Bank w) (m : Memory w) (l : OwnedRowSetup.Layout) (i : Fin (n+1)) (a : Fin l.d)
    (b h K s actual claimed : ℕ) (select : Packet n l.d l.blocks → Selector n K h)
    (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (A : readings m l.header = actual)
    (D : readings m (l.header+1) = claimed) (table : StoredRows (readings m) claimed rows)
    (space : Space l w n b h K s (readings pub 0) actual claimed) (bc : l.bc = h*b)
    (labelFit : l.d^(n+1) ≤ 2^w) (capFit : declarationCap n l.d l.blocks b h s < 2^w)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (left : readings r 14 = a.val) (right : readings r 15 = a.val) :
    let row := Sym2.mk a a
    let values := subtotals itemRow (crossCount b s select) i row
    TestRun pub mac (diagonalChecked n b h K s) r m (diagonalTicks n b h K s l.blocks i a)
      (∀ j, values j = rows row j)
      (Return h actual (head l n b h K s) (readings r) (readings m) values) := by
  intro row values
  let claim := atPair claimed l.d n a.val a.val
  have lim := row_before_bank space a a
  have bank := bank_le_head l n b h K s
  have ca := space.beforeClaim
  have cb := space.beforeBank
  have endRoom := space.endRoom
  apply role_run pub mac r m l i a a b h K s actual claimed _ _ _ values loaded A D space h0 h1 axis
    left right (diagonalChecked_keeps n b h K s)
  intro t mt clearState same
  have cfg := clearState.cfg
  rw [bc] at cfg
  have words (j : Fin (n+1)) : readings mt (claim+j.val) = rows row j :=
    (same _ (claimProtected space _ _ j)).trans (atPair_stored table _ _ le_rfl j)
  apply (diagonalTail_run pub mac t mt i a b s actual claim (readings r 7) select (rows row) cfg
    space.frameFit.endpoints labelFit space.dimension (by omega)
    (fun j => (subtotal_le_cap select i j row).trans_lt capFit) clearState.zeros clearState.declared
    clearState.saved words (fun j => (claimOutside space _ _ j).1) (by dsimp only [claim]; omega)).mono le_rfl Iff.rfl
  rintro z ⟨v,rr,out⟩
  exact ⟨v,rr,fun x hx => out x hx.1⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
