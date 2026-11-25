import OAI.Hierarchy.ProbeStripGeometryFormats
import OAI.Hierarchy.ProbeStripCompiledFormat
import OAI.Hierarchy.ProtocolRAMMenuAlphabetWords
import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProbeStripDirectory
import OAI.Hierarchy.ProbeStripPortDestination
import OAI.Hierarchy.ProbeStripMenuDebitFields
import OAI.Hierarchy.ProbeStripMenuLookup
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceFormat
import OAI.Hierarchy.ProtocolRAMCalendarExtent
import OAI.Hierarchy.ProtocolRAMCalendarGlobalTests
import OAI.Hierarchy.ProtocolRAMCalendarInstalled
import OAI.Hierarchy.ProtocolRAMCommittedPortLayout
import OAI.Hierarchy.TaggedWireShelf

namespace OAI
/-! # Market and commit expressions for the finite geometry of an actual strip

One ordered list of global stock addresses feeds the discrepancy and packet
lookups. The recommendation selects numeric coefficients of the original
packet. An ordinary port credits its own global stock coordinate, while a
cash port targets the sentinel immediately following the commodity bank. -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage PurchaseFrozen
open LinearAlgebra.SpectralBooks.ChordGraph ThreeFlat.RAM
open scoped Fin.CommRing Classical BigOperators

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}
  {q goods digits radix w : ℕ} {D : Type*} [Fintype D]

theorem quoted_read (price offsets stocks : Bank) (addr : Fin digits → Expr) (j : Fin digits)
    (m : Memory w) (r : Word w) :
    (quoted price offsets stocks addr j).eval m r =
      price.read m (offsets.read m ((addr j).eval m r) + stocks.read m ((addr j).eval m r)) := by
  simp [quoted,eval_atRow,AttemptGate.valueTerm,Expr.eval,RowOp.opcode,BinaryOp.eval]

/-- The positive packet word indexes the true alphabet size. The length-zero
packet code and out-of-range words are inert. -/
def mountAlphabet (m : Probe.FixedMenu F edge req box ε tree N) (terms : Bank) (mem : Memory w) :=
  fillSegment terms.base (Fintype.card m.index+1)
    (fun x => (alphabetWord m (x-terms.base) : Word w)) mem

theorem alphabet_read (m : Probe.FixedMenu F edge req box ε tree N) (terms : Bank) (mem : Memory w)
    (i : m.index) (room : Fintype.card m.index+1≤2^w)
    (size : Fintype.card m.index+1≤terms.size) :
    terms.read (mountAlphabet m terms mem) (((Fintype.equivFin m.index i).val+1:ℕ):Word w) =
      ((m.packet i).terms : Word w) := by
  let n := (Fintype.equivFin m.index i).val
  have hn : n < Fintype.card m.index := (Fintype.equivFin m.index i).isLt
  have bound : n+1 < Fintype.card m.index+1 := by omega
  have inside : terms.base ≤ terms.base+(n+1) ∧ terms.base+(n+1)<terms.base+(Fintype.card m.index+1) := by omega
  change terms.read _ ((n+1:ℕ):Word w)=_
  simp only [Bank.read,Fin.val_cast_of_lt (bound.trans_le room),Nat.mod_eq_of_lt (bound.trans_le size),
    mountAlphabet,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left,alphabetWord,dite_eq_left hn]
  exact congrArg (fun u => ((m.packet u).terms : Word w)) ((Fintype.equivFin m.index).symm_apply_apply i)

theorem batch_cash (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr) (e : Fin goods) (cash : slot e=none) :
    let b := batch (q:=q) m test terms menu enabled selectors stocks owner copies maxWidth ports slot
    b.stock e=b.need e := by simp [batch,Batch.need,cash,inventory]

theorem batch_stock (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr) (e : Fin goods) (addr : Expr)
    (physical : slot e=some addr) :
    let b := batch (q:=q) m test terms menu enabled selectors stocks owner copies maxWidth ports slot
    b.stock e = .lookup stocks addr := by simp [batch,physical,inventory]

/-- The actual finite menu is mounted as one RAM lookup table indexed by
the digits read by the physical batch. -/
def mountMenu (m : Probe.FixedMenu F edge req box ε tree N) (menu : Bank)
    (price : (Fin digits→Fin radix)→E→ℝ) (legal : ∀u,price u∈box) (mem : Memory w) :=
  menuAdvice menu (m.word price legal) mem

theorem packet_read (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr)
    (price : (Fin digits→Fin test.radix)→E→ℝ) (legal : ∀u,price u∈box)
    (mem : Memory w) (r : Word w) (v : Fin digits → Fin test.radix)
    (room : test.radix^digits≤2^w) (cap : test.radix^digits≤ menu.size)
    (read : ∀j, (test.quoted j).eval (mountMenu m menu price legal mem) r=((v j).val:Word w)) :
    ((batch (q:=q) m test terms menu enabled selectors stocks owner copies maxWidth ports slot).packet.eval
      (mountMenu m menu price legal mem) r) = (m.word price legal v : Word w) :=
  menu_lookup_word menu (m.word price legal) mem r test.quoted v room cap read

/-- A selected finite template supplies both debit and output bit widths
to the same native slot, including repeated requested occurrences. -/
theorem batch_entries (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr) (i : m.index)
    (mem : Memory w) (r : Word w) (room : 1+Fintype.card m.index≤2^w)
    (e : Fin goods) (j : Fin q) :
    let b := batch (q:=q) m test terms menu enabled selectors stocks owner copies maxWidth ports slot
    (b.packet.eval mem r).val=(Fintype.equivFin m.index i).val+1 →
      (b.perCopy e).eval mem r=(useBits m i (ports e) : Word w) ∧
      (wires m b ports e j).eval mem r=(installedBits m i (ports e) j : Word w) := by
  dsimp only
  intro hit
  exact ⟨entry_read m _ (fun u => useBits m u (ports e)) i mem r room hit,
    entry_read m _ (fun u => installedBits m u (ports e) j) i mem r room hit⟩

/-- Every attempt in the resulting calendar has precisely the row counts
of the actual height, stratum family, and bounded local role list. -/
theorem format_rows {z d k : ℕ} (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (market : Calendar.Market z d k) (repair : Repair q (Fintype.card E))
    (test : StripTest (Fintype.card D)) (globalTests : Calendar.GlobalTests.Layout) (baseline : ℝ)
    (price terms menu enabled selectors : Bank) (old reserve half cash : Bank)
    (owner report : Expr) (priceOut : ℕ→ℕ) (copies maxWidth start indexBits limit : ℕ)
    (mesh : Calendar.Mesh) (finish : ℝ) (prices : PhasePrice) (atTime : Calendar.Attempt) :
    let p := format c m market repair test globalTests baseline price terms menu enabled selectors
      old reserve half cash owner report priceOut copies maxWidth start indexBits limit
    let v := p.atTime mesh finish prices atTime
    Calendar.RowCounts v (Calendar.StockCommit.fresh p.area p.stockSource)
      (Calendar.testedBoard v.failures p.board) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem formatAtStock_area {z d k : ℕ} (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (market : Calendar.Market z d k) (repair : Repair q (Fintype.card E))
    (test : StripTest (Fintype.card D)) (globalTests : Calendar.GlobalTests.Layout) (baseline : ℝ)
    (price terms menu enabled selectors : Bank) (old reserve half cash : Bank)
    (owner report : Expr) (priceOut : ℕ→ℕ) (copies maxWidth start indexBits limit active : ℕ) :
    (formatAtStock c m market repair test globalTests baseline price terms menu enabled selectors
      old reserve half cash owner report priceOut copies maxWidth start indexBits limit active).pricedArea =
    (formatAtStock c m market repair test globalTests baseline price terms menu enabled selectors
      old reserve half cash owner report priceOut copies maxWidth start indexBits limit 0).pricedArea := by
  let form := fun addr => formatAtStock c m market repair test globalTests baseline
    price terms menu enabled selectors old reserve half cash owner report priceOut copies maxWidth start indexBits limit addr
  let origin := form 0
  let shape (length : ℕ) : Calendar.StockCommit.Area :=
    let verdict := Calendar.PostLayout.column origin.maskStart indexBits market.rows (17+3*Fintype.card E+length)
    {origin.pricedArea with start := verdict+1+origin.occurrences}
  have lengths (addr : ℕ) : (form addr).batch.batch.quotes.length = Fintype.card D := by
    change (List.ofFn (quoted price (Calendar.GlobalTests.offsets globalTests) {old with base:=addr} c.digit)).length = _
    simp only [List.length_ofFn]
  change shape (form active).batch.batch.quotes.length = shape (form 0).batch.batch.quotes.length
  exact congrArg shape ((lengths active).trans (lengths 0).symm)


end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
