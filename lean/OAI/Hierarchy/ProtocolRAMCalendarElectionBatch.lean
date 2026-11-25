import OAI.Hierarchy.ProbeStripElection
import OAI.Hierarchy.ProbeStripInputEnd
import OAI.Hierarchy.ProtocolRAMBelow
import OAI.Hierarchy.ProtocolRAMPortPadding

namespace OAI
/-! # The whole padded local menu election uses only earlier geometry and the new failed word -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage Calendar
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical

variable {F E A Y : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] [Fintype Y]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N q w cut : ℕ}

theorem Channels.Before.padded_election (c : Channels Y E) (old : c.Before cut)
    (m : Probe.FixedMenu F edge req box ε tree N)
    (test : StripTest (Fintype.card Y)) (price offsets terms recommendations mask selectors stocks : Bank)
    (copies maxWidth padded : ℕ) (left right : Memory w) (r : Word w)
    (same : Below cut left right) (active : mask.read left r=mask.read right r)
    (visible : cut<2^w) (cap : maxWidth<2^w) (roles : Fintype.card E≤padded)
    (priceEnd : price.base+price.size≤cut) (offEnd : offsets.base+offsets.size≤cut)
    (stockEnd : stocks.base+stocks.size≤cut) (recEnd : recommendations.base+recommendations.size≤cut)
    (termsEnd : terms.base+terms.size≤cut) :
    let test:=tested test price offsets stocks c.digit
    let b:=PortPadding.batch padded (batch (q:=q) m test terms recommendations mask selectors stocks .row copies maxWidth
      (Fintype.equivFin E).symm c.slot)
    b.packet.eval left r=b.packet.eval right r ∧
      b.termCount.read left (b.packet.eval left r)=b.termCount.read right (b.packet.eval right r) ∧
      (b.selected left r ↔ b.selected right r) := by
  let t:=tested test price offsets stocks c.digit
  let b:=batch (q:=q) m t terms recommendations mask selectors stocks .row copies maxWidth
    (Fintype.equivFin E).symm c.slot
  have addr (a : Y) : (c.address a).eval left r=(c.address a).eval right r :=
    same.expr _ _ (Expr.fits_of_inputEnd _ (old.address a) visible) le_rfl
  have quotes (i : Fin (Fintype.card Y)) : (t.quoted i).eval left r=(t.quoted i).eval right r := by
    change (quoted price offsets stocks c.digit i).eval left r=(quoted price offsets stocks c.digit i).eval right r
    rw [quoted_read,quoted_read,show (c.digit i).eval left r=(c.digit i).eval right r from addr _,
      same.bank offsets _ offEnd,same.bank stocks _ stockEnd,same.bank price _ priceEnd]
  have previous (i : Fin (Fintype.card E)) (x : Expr) (hit : c.slot i=some x) :
      stocks.read left (x.eval left r)=stocks.read right (x.eval right r) := by
    unfold Channels.slot at hit
    cases h : c.account ((Fintype.equivFin E).symm i) with
    | none=>simp [h] at hit
    | some a=>
      have eqn : c.address a=x := by simpa [h] using hit
      subst x
      rw [addr,same.bank stocks _ stockEnd]
  obtain ⟨key,letters,vote⟩:=election (q:=q) m t terms recommendations mask selectors stocks copies maxWidth
    (Fintype.equivFin E).symm c.slot left right r active quotes
    (same.bank recommendations _ recEnd) (same.bank terms _ termsEnd) previous
  exact ⟨key,letters,(PortPadding.selected b left r roles cap).trans
    (vote.trans (PortPadding.selected b right r roles cap).symm)⟩

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
