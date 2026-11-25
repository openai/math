import OAI.Computability.BorderVNP.PackedBankBoxMerged
import OAI.Computability.BorderVNP.PackedBankBoxOrdinal
import OAI.Computability.BorderVNP.PackedCellWireView
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-! # Actual cable bases of a sewn paid-term site

Each paid-site input row names either an original term edge or a feeder
from a physical terminal. Its public base is the shared internal or supplied
wire address of that cable in the owning cell. The resulting box reads the
same paid-table addresses as the actual sewn output factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidPhysical

open Crossing Crossing.CellBox PaidBox CellSparse Shortening Shortening.CombiningStep Shortening.SeedIntervals
open private bundleWidth from OAI.Computability.BorderVNP.PackedBankBoxLayout
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
  {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout

variable (s : A) (a : Fin e.count) (v : (e.net a).Site)

/-- The sewn site's name in the actual combining-step output. -/
def site : (G e p bin perm positive first q).Site := .inr ⟨s,.inr (.inr ⟨a,v⟩)⟩

/-- Incidence of a physical internal term cable or feeder at this bank site. -/
def cable (r : PaidBox.Bundle (e.net a) v) :
    {u : (G e p bin perm positive first q).Edge // (G e p bin perm positive first q).src u =
      site e p bin perm positive first q s a v ∨ (G e p bin perm positive first q).dst u =
        site e p bin perm positive first q s a v} := by
  rcases r with ⟨u,hu⟩ | ⟨u,hu⟩
  · refine ⟨.inr (.inr ⟨s,.inr (.inr ⟨a,u⟩)⟩), hu.imp ?_ ?_⟩ <;> exact congrArg (site e p bin perm positive first q s a)
  · exact ⟨.inr (.inr ⟨s,.inr (.inl (a,u))⟩),Or.inr (congrArg (site e p bin perm positive first q s a) hu)⟩

omit [Fintype P] in
private theorem cable_width (r : PaidBox.Bundle (e.net a) v) :
    (G e p bin perm positive first q).width (cable e p bin perm positive first q s a v r).val =
      (q s).val a * bundleWidth (e.net a) v r := by cases r <;> rfl

/-- The actual profile-internal cable words as a restriction of the complete sewn assignment. -/
def profileWires (y : (G e p bin perm positive first q).Assignment) :
    (e.profile (blocks p.layout bin perm m s) (q s).val).Assignment :=
  fun u => y (.inr (.inr ⟨s,u⟩))

omit [Fintype P] in
/-- Exact local factor of the sewn pack, read directly at the old one-copy table addresses. -/
theorem site_read (y : (G e p bin perm positive first q).Assignment) (x : Ports bits) :
    (G e p bin perm positive first q).read (output e p bin perm positive first q).table y x
      (site e p bin perm positive first q s a v) =
    ∏ i : Fin ((q s).val a), e.entry (selectedEntry e a v (q s).val (profileWires e p bin perm positive first q s y) i) :=
  rfl

private def oneLane (r : PaidBox.Bundle (e.net a) v) (k : Fin (bundleWidth (e.net a) v r)) :
    Lane (e.net a) v := Equiv.sumSigmaDistrib (fun r => Fin (bundleWidth (e.net a) v r)) ⟨r,k⟩

omit [NeZero D] in
private theorem orderedLane (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v)))
    (k : Fin (widths (e.net a) v r)) :
    (laneOrder (e.net a) v).symm (finSigmaFinEquiv ⟨r,k⟩) =
      oneLane e a v ((Fintype.equivFin _).symm r) k := by
  let read (z : Σ t, Fin (widths (e.net a) v t)) := oneLane e a v ((Fintype.equivFin _).symm z.1) z.2
  exact congrArg read ((finSigmaFinEquiv (n := widths (e.net a) v)).symm_apply_apply ⟨r,k⟩)

omit [Fintype P] in
private theorem readLane (y : (G e p bin perm positive first q).Assignment) (i : Fin ((q s).val a))
    (r : PaidBox.Bundle (e.net a) v) (k : Fin (bundleWidth (e.net a) v r)) :
    y (cable e p bin perm positive first q s a v r).val
      (Fin.cast (cable_width e p bin perm positive first q s a v r).symm (finProdFinEquiv (i,k))) =
    bankLanes e.net antipodalPosition (fun u => by obtain ⟨i,b⟩ := u; cases b <;> simp [antipodalPosition])
      (q s).val (profileWires e p bin perm positive first q s y) a v i (oneLane e a v r k) := by
  cases r <;> rfl

variable {C : Type} (cell : (G e p bin perm positive first q).Site → C)
  {edges ports sites : ℕ} (edgeID : (G e p bin perm positive first q).Edge ↪ Fin edges)
  (portID : P ↪ Fin ports) (aux : (G e p bin perm positive first q).Site → ℕ)

private abbrev V := site e p bin perm positive first q s a v
private abbrev c := cell (V e p bin perm positive first q s a v)

/-- Canonical cable-base column for the site's frozen public packet. -/
noncomputable def bases (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v))) : ℕ :=
  CellAddresses.wireBase (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell)
    edgeID portID aux ⟨V e p bin perm positive first q s a v,rfl⟩
      (cable e p bin perm positive first q s a v ((Fintype.equivFin _).symm r))

/-- With the actual shared cable bases installed, every copied lane is the
one selected by the paid profile network on the cell's physical wire assignment. -/
theorem physical_data
    (g : Fin (CellAddresses.guessedSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell)) → Bool)
    (z : Fin (CellAddresses.siteSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell) aux) → Bool)
    (x : Fin (CellAddresses.suppliedSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell)) → Bool)
    (i : Fin ((q s).val a)) (k : Fin (arity e a v)) :
    let G := G e p bin perm positive first q
    let c := cell (V e p bin perm positive first q s a v)
    let b := bases e p bin perm positive first q s a v cell edgeID portID aux
    let bank := lookup (CellAddresses.bank G cell c aux g z x)
    let y := CellAddresses.assignment G cell c edgeID portID g x
    PaidBinding.data (widths (e.net a) v) ((q s).val a) b bank i k =
      PaidBox.data e a v (q s).val (profileWires e p bin perm positive first q s y) i k := by
  dsimp only
  let G := G e p bin perm positive first q
  let u := V e p bin perm positive first q s a v
  let c := cell u
  let w := widths (e.net a) v
  let b := bases e p bin perm positive first q s a v cell edgeID portID aux
  let bank := lookup (CellAddresses.bank G cell c aux g z x)
  let y := CellAddresses.assignment G cell c edgeID portID g x
  obtain ⟨⟨r,k⟩,rfl⟩ := (finSigmaFinEquiv (n := w)).surjective k
  let u' := (Fintype.equivFin (PaidBox.Bundle (e.net a) v)).symm r
  let edge := cable e p bin perm positive first q s a v u'
  let lane := Fin.cast (cable_width e p bin perm positive first q s a v u').symm (finProdFinEquiv (i,k))
  have hv := CellAddresses.assignment_at G cell c edgeID portID aux g z x ⟨u,rfl⟩ edge lane
  have hpos : lane.val = i.val*w r+k.val := by simp [lane,u',w,widths,Nat.mul_comm,Nat.add_comm]
  change PaidBinding.data w ((q s).val a) b bank i (finSigmaFinEquiv ⟨r,k⟩) = _
  rw [PaidBinding.data,(finSigmaFinEquiv (n := w)).symm_apply_apply ⟨r,k⟩, PaidBox.data,orderedLane]
  exact (by simpa only [hpos,Nat.add_assoc,b,bases,bank,u',edge] using hv :
    bank (b r + i.val*w r+k.val) = y edge.val lane).trans
    (readLane e p bin perm positive first q s a v y i u' k)

local notation3 "G₀" => G e p bin perm positive first q
local notation3 "v₀" => V e p bin perm positive first q s a v
local notation3 "c₀" => cell v₀
local notation3 "copies₀" => Subtype.val (q s) a
local notation3 "bases₀" => bases e p bin perm positive first q s a v cell edgeID portID aux
local notation3 "widths₀" => widths (e.net a) v

variable (g : Fin (CellAddresses.guessedSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell)) → Bool)
  (z : Fin (CellAddresses.siteSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell) aux) → Bool)
  (x : Fin (CellAddresses.suppliedSize (G e p bin perm positive first q) cell (c e p bin perm positive first q s a v cell)) → Bool)

local notation3 "bank₀" => lookup (CellAddresses.bank G₀ cell c₀ aux g z x)
local notation3 "y₀" => CellAddresses.assignment G₀ cell c₀ edgeID portID g x
local notation3 "profile₀" => profileWires e p bin perm positive first q s y₀

private theorem entry_eq (i : Fin copies₀) :
    PaidBinding.entryAt copies₀ e a v bases₀ bank₀ i = selectedEntry e a v (q s).val profile₀ i := by
  let encode (b : Lane (e.net a) v → Bool) : e.Entry :=
    ⟨a,v,(fun u k => b (.inl ⟨u,k⟩)),(fun u k => b (.inr ⟨u,k⟩))⟩
  let incoming := fun l => PaidBinding.data widths₀ copies₀ bases₀ bank₀ i (laneOrder (e.net a) v l)
  let exactBits := bankLanes e.net antipodalPosition (fun u => by obtain ⟨j,b⟩ := u; cases b <;> simp [antipodalPosition])
    (q s).val profile₀ a v i
  change encode incoming = encode exactBits
  apply congrArg encode
  funext l
  have h := physical_data e p bin perm positive first q s a v cell edgeID portID aux g z x i
    (laneOrder (e.net a) v l)
  exact h.trans (congrArg exactBits ((laneOrder (e.net a) v).symm_apply_apply l))

private theorem canonical_eq :
    PaidBinding.canonical widths₀ copies₀ bases₀ bank₀ = siteBank e a v (q s).val profile₀ := by
  have hd := funext fun i => funext fun k =>
    physical_data e p bin perm positive first q s a v cell edgeID portID aux g z x i k
  unfold PaidBinding.canonical siteBank
  rw [hd]

variable (siteID : (G e p bin perm positive first q).Site ↪ Fin sites) (id : ℕ) (boxes : List (List Factor))
local notation3 "off₀" => CellAddresses.siteBase G₀ cell c₀ siteID aux ⟨v₀,rfl⟩
local notation3 "dir₀" => PaidBinding.fragment widths₀ copies₀ off₀ id bases₀ boxes

/-- The emitted merged segment accepts exactly the intended private site word. Its
canonical value depends solely on the shared guessed and supplied cables, so it
can be used directly in the unique-staging sum for the entire cell. -/
theorem staging_iff (hsize : aux v₀ = copies₀*arity e a v + copies₀*arity e a v) :
    (∀ r ∈ (dir₀).records, r.Valid boxes bank₀) ↔ id < boxes.length ∧
      ∀ k : Fin (aux v₀), CellAddresses.siteWords G₀ cell c₀ siteID aux z ⟨v₀,rfl⟩ k =
        siteBank e a v (q s).val profile₀ k.val := by
  change (∀ r ∈ (BankPacket.Paid.rows widths₀).map
    (BankPacket.RecordCode.read (PaidBinding.fields widths₀ copies₀ off₀ id bases₀)), r.Valid boxes bank₀) ↔ _
  rw [PaidBinding.valid_iff, canonical_eq e p bin perm positive first q s a v cell edgeID portID aux g z x]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi,fun k => ?_⟩
    exact (CellAddresses.site_at G₀ cell c₀ aux siteID g z x ⟨v₀,rfl⟩ k).symm.trans
      (h k.val (k.isLt.trans_le hsize.le))
  · rintro ⟨hi,h⟩
    refine ⟨hi,fun t ht => ?_⟩
    let k : Fin (aux v₀) := ⟨t,ht.trans_le hsize.symm.le⟩
    exact (CellAddresses.site_at G₀ cell c₀ aux siteID g z x ⟨v₀,rfl⟩ k).trans (h k)

/-- The actual merged-ID packet reads precisely the entries whose product is the
physical paid-term table of the sewn pack on this cell's wire assignment. -/
theorem observations_and_read (position : e.Entry → ℕ)
    (hbox : boxes.getD id [] = [tableFactor e position a v])
    (hvalid : ∀ r ∈ (dir₀).records, r.Valid boxes bank₀) (ports : Ports bits) :
    let entries := fun i => selectedEntry e a v (q s).val profile₀ i
    (dir₀).observations bank₀ = some (List.ofFn fun i => (false,some (position (entries i)))) ∧
    (G₀).read (output e p bin perm positive first q).table y₀ ports v₀ = ∏ i, e.entry (entries i) := by
  refine ⟨?_,site_read e p bin perm positive first q s a v y₀ ports⟩
  rw [PaidBinding.observations _ _ _ _ _ _ _ _ _ _ hbox hvalid]
  congr 2
  funext i
  rw [entry_eq e p bin perm positive first q s a v cell edgeID portID aux g z x i]

omit [NeZero D] in
/-- The slot supplied by the stable merged-ordinal frame resolves to the paid
factor when the fixed one-copy site directory is installed at that public row. -/
theorem box_lookup {S k w : ℕ} (position : e.Entry → ℕ) (input : BankBoxOrdinal.Input S k w → Bool)
    (owner : Fin S → ℕ) (table : Fin S → List (List Factor)) (site : Fin S)
    (ho : ∀ i, BankBoxOrdinal.ownerWord input i = owner i)
    (hc : ∀ i, BankBoxOrdinal.countWord input i = (table i).length)
    (room : ∀ c, (BankBoxOrdinal.table owner table c).length < 2^w)
    (paid : table site = [[tableFactor e position a v]]) :
    (BankBoxOrdinal.table owner table (owner site)).getD
      (ParseBatchSort.value (fun b => (BankBoxOrdinal.frame S k w).eval input (site,b))) [] =
        [tableFactor e position a v] := by
  let j : Fin (table site).length := ⟨0,by simp [paid]⟩
  have h := BankBoxOrdinal.frame_getD input owner table ho hc room site j []
  have hj : (table site).get j = [tableFactor e position a v] := by
    change (table site)[0]'j.isLt = _
    simp [paid]
  change (BankBoxOrdinal.table owner table (owner site)).getD
    (ParseBatchSort.value (fun b => (BankBoxOrdinal.frame S k w).eval input (site,b)) + 0) [] = _ at h
  rw [Nat.add_zero] at h
  exact h.trans hj

end Packing.PaidPhysical

end BorderVNP
end Computability
end OAI
