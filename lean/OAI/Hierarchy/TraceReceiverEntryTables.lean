import OAI.Hierarchy.TraceReceiverEntryFrame
import OAI.Hierarchy.GridReceiverIntervalSchedule

namespace OAI
/-! # Retaining the four actual classifier and ancestor inputs across table mounting -/
namespace Hierarchy.TraceReceiverEntryTables
open ThreeFlat Diagonal.TickWorkspace Computability.VPVNP.BurstRAM
open GridThrough GridPinPublisher
open scoped Fin.CommRing
noncomputable section

set_option quotPrecheck false
variable {w u k n q pins pars sel text compact rails bits N stages full m f roots lib : ℕ}
local notation "P" => canonical w k n q pins pars sel text compact rails bits N stages full (2*2^(w/2))
local notation "J" => GridDescription.sector w
local notation "g" => GridPinArena.slab w
local notation "S" => stride u
local notation "K" => ((20*(w+1)+2)^(k+2))
local notation "W" => (64*w)
local notation "owners" => (GridReceiverTickDirectory.banks w u).owners
local notation "target" => ((GridReceiverTickDirectory.banks w u).scratch+1)

/-- The exact last member of the conjunction produced by the genuine
TraceReceiverTablesMount.run, at the receiver's S38 library and 26J gate base. -/
def TableFrame (w u lib : ℕ) (elected tables : Memory (64*w)) : Prop :=
  ∀ a,a < 26*GridDescription.sector w → (a < base u 38 ∨ base u 38+lib ≤ a) → tables a=elected a

variable {elected tables : Memory (64*w)}

theorem window (keep : TableFrame w u lib elected tables) (pos : 0 < w)
    (upper : u^10 ≤ 5*w) (size : lib ≤ S) (a : ℕ) (lo : 14*J ≤ a) (hi : a < 26*J) :
    tables a=elected a := by
  have sep:=TraceReceiverOwnerMount.sector pos upper
  exact keep a hi (.inr (by change 39*S+lib ≤ a;omega))

/-- The emitted resource matrix, both class/owner arrays and every original
lane's terminal destination are exactly the elected machine's rows. -/
theorem count_inputs (small : GridPinArena.Small w P bits full (stages*full) K)
    (Q : FactorPinIntervals.Layout (Cell k n×Fin q) bits N pins) (ht : 0<(n+1)^k*q)
    (cost : Fin N → Fin m → ℕ) (lane : Fin full → Fin N)
    (src : CountInputs P Q ht w cost lane elected) (keep : TableFrame w u lib elected tables)
    (pos : 0 < w) (upper : u^10 ≤ 5*w) (size : lib ≤ S) : CountInputs P Q ht w cost lane tables := by
  have smallJ:=(GridPinArena.scales w pos).1
  have matrix : N*(k+2) ≤ g:=small.resource
  have items : N ≤ g:=(Nat.le_mul_of_pos_right _ (by omega : 0 < k+2)).trans matrix
  have staged:=small.staged;have cap:=small.full
  apply CountInputs.keep src
  · intro i;have hi:=i.isLt;change tables (15*J+g+i.val)=_
    apply window keep pos upper size <;> omega
  · intro i;have hi:=i.isLt;change tables (15*J+3*g+i.val)=_
    apply window keep pos upper size <;> omega
  · intro i;have hi:=Nat.mul_le_mul_right (k+2) i.isLt;rw [Nat.succ_mul] at hi
    change tables (14*J+i.val*(k+2)+1)=_
    apply window keep pos upper size <;> omega
  · intro j;have hi:=j.isLt;change tables (16*J+g+stages*full+j.val)=_
    apply window keep pos upper size <;> omega

/-- Both indirect reads of the canonical S5 passes are in range because the
physical stored words are the actual finite owner and destination ordinals. -/
theorem prefix_owners (R : GridPinArena.Scalars W P bits full K g)
    {Q : FactorPinIntervals.Layout (Cell k n×Fin q) bits N pins} {ht : 0<(n+1)^k*q}
    {cost : Fin N → Fin m → ℕ} {lane : Fin full → Fin N} {mem : Memory W}
    (src : CountInputs P Q ht w cost lane mem) : PrefixOwners P mem := by
  exact src.prefix rfl rfl R.ticksFit R.itemsFit R.within

theorem table_reads (pos : 0 < w) (upper : u^10 ≤ 5*w) (size : lib ≤ S)
    (old : 8*(f+roots) ≤ S) (rootFit : roots ≤ g) (keep : TableFrame w u lib elected tables)
    (a : ℕ) (rd : TraceReceiverOwnerMount.Reads u f roots owners target a) : tables a=elected a := by
  have sep:=TraceReceiverOwnerMount.sector pos upper
  have scales:=GridPinArena.scales w pos
  have positive : 0 < g:=Nat.two_pow_pos _
  rcases TraceReceiverOwnerMount.read_bands old rootFit rd with h|h|h
  · change 45*S ≤ a ∧ a < 46*S at h
    apply keep a (by omega) (.inr (by change 39*S+lib ≤ a;omega))
  · exact window keep pos upper size a (by omega) (by omega)
  · exact window keep pos upper size a (by omega) (by omega)

theorem after_interval_reads (R : GridPinArena.Scalars W P bits full K g)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (size : lib ≤ S) (old : 8*(f+roots) ≤ S) (rootFit : roots ≤ g)
    (keep : TableFrame w u lib elected tables) (ready : PrefixOwners P tables)
    (a : ℕ) (rd : TraceReceiverOwnerMount.Reads u f roots owners target a) :
    (P).intervalMemory (base u 5) tables a=elected a :=
  (TraceReceiverEntryFrame.interval_inputs R large lower upper bitsFit old rootFit tables ready a rd).trans
    (table_reads (by omega) upper size old rootFit keep a rd)

/-- The S20 journal below its stop, S43/S44 and low shifted inputs agree
with their original elected values after mounting the decoder, slots, and owners. -/
theorem original (R : GridPinArena.Scalars W P bits full K g)
    (room : TraceReceiverOwnerMount.Room W u f roots owners target)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (size : lib ≤ S) (keep : TableFrame w u lib elected tables) (ready : PrefixOwners P tables)
    (a : ℕ) (old : a < base u 1 ∨ (base u 20 ≤ a ∧ a < base u 38) ∨ (base u 43 ≤ a ∧ a < base u 45)) :
    TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) tables) a=elected a := by
  have sep:=TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  change a < 2*S ∨ (21*S ≤ a ∧ a < 39*S) ∨ (44*S ≤ a ∧ a < 46*S) at old
  refine (TraceReceiverEntryFrame.after R room large lower upper bitsFit tables ready a ?_).trans
    (keep a (by omega) ?_)
  · change a < 2*S ∨ (13*S ≤ a ∧ a < 46*S) ∨ 16*J ≤ a;omega
  · change a < 39*S ∨ 39*S+lib ≤ a;omega

/-- The decoded S38 library and every mounted 26J-and-above virtual decoder word
are retained with their genuine post-packing/post-dictionary contents. -/
theorem installed (R : GridPinArena.Scalars W P bits full K g)
    (room : TraceReceiverOwnerMount.Room W u f roots owners target)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (size : lib ≤ S) (ready : PrefixOwners P tables) :
    let out:=TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) tables)
    (∀ i < lib,out (base u 38+i)=tables (base u 38+i)) ∧ ∀ a,26*J ≤ a → out a=tables a := by
  intro out
  have same:=TraceReceiverEntryFrame.after R room large lower upper bitsFit tables ready
  constructor
  · intro i hi
    apply same _ (.inr (.inl ?_))
    change 13*S ≤ 39*S+i ∧ 39*S+i < 46*S
    omega
  · intro a hi;exact same a (.inr (.inr (by omega)))

/-- The second S17 pass reads the first classifier's original keys, elected
factor owners, decoded target, resource rows and true destination journal. -/
theorem after_classifier (R : GridPinArena.Scalars W P bits full K g)
    (room : TraceReceiverOwnerMount.Room W u f roots owners target)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (size : lib ≤ S) (keep : TableFrame w u lib elected tables) (ready : PrefixOwners P tables) :
    let out:=TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) tables)
    (∀ v < g,out (15*J+g+v)=elected (15*J+g+v)) ∧
    (∀ v < g,out (15*J+3*g+v)=elected (15*J+3*g+v)) ∧
    out (15*J+20*g+1)=elected (15*J+20*g+1) ∧
    (∀ v < g,out (14*J+v)=elected (14*J+v)) ∧
    ∀ a,16*J ≤ a → a < 26*J → out a=elected a := by
  intro out
  have pos : 0 < w:=by omega
  have scales:=GridPinArena.scales w pos
  have positive : 0 < g:=Nat.two_pow_pos _
  obtain ⟨key,own,slot,resources,high⟩:=TraceReceiverEntryFrame.after_classifier R room large lower upper bitsFit tables ready
  have held (a : ℕ) (lo : 14*J ≤ a) (hi : a < 26*J) : tables a=elected a :=
    window keep pos upper size a lo hi
  refine ⟨?_,?_,slot.trans (held (15*J+20*g+1) (by omega) (by omega)),?_,?_⟩
  · intro v h;exact (key v h).trans (held (15*J+g+v) (by omega) (by omega))
  · intro v h;exact (own v h).trans (held (15*J+3*g+v) (by omega) (by omega))
  · intro v h;exact (resources v h).trans (held (14*J+v) (by omega) (by omega))
  · intro a lo hi;exact (high a lo).trans (held a (by omega) hi)

end
end Hierarchy.TraceReceiverEntryTables

end OAI
