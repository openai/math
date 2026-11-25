import OAI.Hierarchy.TaggedWideDateApertures
import OAI.Hierarchy.TaggedWideCompiledControlRead
import OAI.Hierarchy.TaggedWideControlFields

namespace OAI
/-! # Original funded role pages at a signed packet endpoint -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM DescriptorExpr
open ProbeStage ProbeStage.CoreBoard ProbeStage.ReportSockets ProbeStage.CoreBoard.HistoryRoles WireTelescope NamedAperture Tagged PassiveWindow
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM DatedRoleSheets
open scoped Classical Fin.CommRing BigOperators
section
variable {h W k attempts N native cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
local notation "sites" => siteLast h (2^W) k+1
local notation "D" => stride k S.degree attempts
local notation "ends" => sorted S π depth mark ∘ rows
local notation "port" => named S π depth mark unique rows
variable (n start bits : ℕ) (s : Fin (siteLast h (2^W) k+1)) (qty id : Fin N→ℕ) (bounded : ∀i,qty i≤cap)
    {total : Widths (siteLast h (2^W) k+1)} (shape : installedWidths (sorted S π depth mark ∘ rows) qty=total) (m : Memory native)
    (published : ∀f,roleFact n S π depth mark unique rows start qty id m f)
    (table : Bank) (here : Expr) (reg : Word native) (one : 1<2^native) (wide : ∀i,qty i<2^native)
    (wordRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤2^native) (bankRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤2^bits)
    (atSite : table.read m (here.eval m reg)=((s.val*(stride k S.degree attempts):ℕ):Word native))
    (order : StrictMono id) (idFits : ∀i,id i<2^native) (siteFits : (siteLast h (2^W) k+1)≤2^native)
local notation "slot" => PacketNeighbor.localSlot ends qty port (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)
  (named_coordinate S π depth mark unique rows) s
local notation "parts" => carried ends qty s bounded slot shape
local notation "row" => columns («D»:=D) n start sites bits table here


include published one wide wordRoom bankRoom atSite order idFits siteFits in
/-- The original before/post role sheet provides every geometric operand in
the native signed compactor. The released/installed portion is taken from
the elected ballot at the same physical site. -/
theorem signed_endpoint (capFit : cap<2^native) (room : ∀p : (portGraph sites).Port s,total p.val.1<2^native)
    (low : Fin D→Expr) (portion : (portGraph sites).Port s→ℕ)
    (elected : ∀q,((low q).eval m reg).val=((parts).owner q).elim 0 portion) :
    EndpointReads m reg parts row low portion ∧ ApertureGeometry m reg parts row := by
  have actual:=neighbors S π depth mark unique rows n start bits s qty id bounded shape m published
    table here reg one wide wordRoom bankRoom atSite
  have geo:=aperture_geometry m reg ends qty bounded slot shape row actual room
  have fields:=dated_apertures S π depth mark unique rows n start bits s qty id bounded shape m published
    table here reg one wide wordRoom bankRoom atSite order idFits siteFits capFit room
  refine ⟨⟨?_,?_,elected,?_,?_⟩,geo⟩
  · intro i
    have inside : (parts).base i<2^native:=by
      by_cases live:i∈Set.range slot
      · obtain ⟨a,rfl⟩:=live
        have owned:=(seat_value ends qty s bounded slot shape a).1
        exact (Nat.le_add_right ..).trans_lt (((parts).top _ _ owned).trans_lt (room _))
      · rw [(seat_vacant ends qty s bounded slot shape i live).2.2]
        exact pow_pos (by decide) _
    rw [fields.1 i,Fin.val_cast_of_lt inside]
  · intro i
    rw [fields.2.1 i,Fin.val_cast_of_lt (((parts).within i).trans_lt capFit)]
  · intro i p own live
    change ((pageRead (bank n start (sites*D) bits 2) table here i).eval m reg).val = _
    rw [actual.siteAt i p own live,Fin.val_cast_of_lt ((PacketNeighbor.other p).isLt.trans_le siteFits)]
  · intro i vacant
    by_contra ne
    have visible:=(geo.owned i).mpr (Nat.pos_of_ne_zero ne)
    simp [vacant] at visible

end

/-- Partial application to the three genuine role fields fixes the original
row order and the actual processing heap. Only numeric word room and the
party's address on this heap remain to select its port ordering. -/
theorem ports_of_sheet {h W k attempts N native n start depth rom : ℕ} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {mark : Marks h W k attempts} {unique : Exclusive mark}
    {rows : Fin N≃Source S π depth mark} {qty id : Fin N→ℕ} {m : Memory native}
    (entry : ∀f,roleFact n S π depth mark unique rows start qty id m f)
    (strideROM : RoleROM.Mounted rom (fun i : Fin (siteLast h (2^W) k+1)=>i.val*stride k S.degree attempts) m) :
    ∀ cap (s : Fin (siteLast h (2^W) k+1)) (bounded : ∀i,qty i≤cap)
      (total : Widths (siteLast h (2^W) k+1)) (shape : installedWidths (sorted S π depth mark ∘ rows) qty=total)
      (here : Expr) (reg : Word native) (_found : here.eval m reg=(s.val:Word native)),
      let deg:=stride k S.degree attempts
      let size:=siteLast h (2^W) k+1
      let bankBits:=ProtocolRAMPurchaseSampler.bits (size*deg)
      let slot:=PacketNeighbor.localSlot (sorted S π depth mark ∘ rows) qty
        (named S π depth mark unique rows) (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S) (named_coordinate S π depth mark unique rows) s
      let actual:=carried (sorted S π depth mark ∘ rows) qty s bounded slot shape
      let row:=columns (D:=deg) n start size bankBits (RoleROM.bank rom size) here
      1<2^native → (∀i,qty i<2^native) → size≤2^native → size*deg≤2^native →
      PacketTurns.NeighborReads m reg actual (fun q=>(row q).width) (fun q=>(row q).opposite) := by
  intro cap s bounded total shape here reg found deg size bankBits slot actual row one paid siteRoom spanRoom
  exact DatedRoleSheets.neighbors S π depth mark unique rows n start bankBits s qty id bounded shape
    m entry _ here reg one paid spanRoom (ProtocolRAMPurchaseSampler.lt_span _).le
    (RoleROM.read strideROM here reg s siteRoom found)

theorem endpoints_of_sheet {h W k attempts N native n start depth rom : ℕ} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {mark : Marks h W k attempts} {unique : Exclusive mark}
    {rows : Fin N≃Source S π depth mark} {qty id : Fin N→ℕ} {m : Memory native}
    (entry : ∀f,roleFact n S π depth mark unique rows start qty id m f)
    (strideROM : RoleROM.Mounted rom (fun i : Fin (siteLast h (2^W) k+1)=>i.val*stride k S.degree attempts) m) :
    ∀ cap (s : Fin (siteLast h (2^W) k+1)) (bounded : ∀i,qty i≤cap)
      (total : Widths (siteLast h (2^W) k+1)) (shape : installedWidths (sorted S π depth mark ∘ rows) qty=total)
      (here : Expr) (reg : Word native) (_found : here.eval m reg=(s.val:Word native)),
      let deg:=stride k S.degree attempts
      let size:=siteLast h (2^W) k+1
      let bankBits:=ProtocolRAMPurchaseSampler.bits (size*deg)
      let slot:=PacketNeighbor.localSlot (sorted S π depth mark ∘ rows) qty
        (named S π depth mark unique rows) (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S) (named_coordinate S π depth mark unique rows) s
      let actual:=carried (sorted S π depth mark ∘ rows) qty s bounded slot shape
      let row:=columns (D:=deg) n start size bankBits (RoleROM.bank rom size) here
      1<2^native → (∀i,qty i<2^native) → size≤2^native → size*deg≤2^native →
      StrictMono id → (∀i,id i<2^native) → cap<2^native →
      (∀p : (portGraph size).Port s,total p.val.1<2^native) →
      ∀(low : Fin deg→Expr) (portion : (portGraph size).Port s→ℕ),
      (∀q,((low q).eval m reg).val=(actual.owner q).elim 0 portion) →
      EndpointReads m reg actual row low portion ∧ ApertureGeometry m reg actual row := by
  intro cap s bounded total shape here reg found deg size bankBits slot actual row one paid siteRoom spanRoom
    ord names small totals low portion elected
  apply signed_endpoint S π depth mark unique rows n start bankBits s qty id bounded shape m entry
    _ here reg one paid spanRoom (ProtocolRAMPurchaseSampler.lt_span _).le
    (RoleROM.read strideROM here reg s siteRoom found) ord names siteRoom small totals low portion elected

/-- A paid ballot cell directly supplies the leading width to the ordinary
signed control scan, including a zero at unoccupied sites. -/
theorem signed_ballot_low {D W sites : ℕ} (base fields first : ℕ) (side : Bool) (q : Fin D)
    (s : Fin sites) (input : Memory W) (sized : first+(D+D)≤fields) (room : sites*fields≤2^W)
    {amount : ℕ} (paid : (input (base+(s.val*fields+(first+side.toNat*D+q.val)))).val=amount) :
    ((lowFieldFrom first sites base fields side q).eval input (s.val:Word W)).val=amount := by
  rw [low_at_from base fields first side q s input sized room]
  exact paid

theorem signed_low_from_word {D W sites : ℕ} (base fields first : ℕ) (side : Bool) (q : Fin D)
    (s : Fin sites) (input : Memory W) (sized : first+(D+D)≤fields) (room : sites*fields≤2^W)
    {V : Type} (who : Option V) (rate : V→ℕ) (safe : ∀p,rate p<2^W)
    (slot : Fin fields) (number : slot.val=first+side.toNat*D+q.val)
    (stored : input (base+1+s.val*fields+slot.val)=(↑(who.elim (0:ℕ) rate):Word W)) :
    ((lowFieldFrom first sites (base+1) fields side q).eval input (s.val:Word W)).val=who.elim 0 rate := by
  apply signed_ballot_low (base+1) fields first side q s input sized room
  rw [←number,←Nat.add_assoc,stored]
  have fit : who.elim (0:ℕ) rate < 2^W := by
    cases who with
    | none => exact Nat.two_pow_pos _
    | some p => exact safe p
  exact Fin.val_cast_of_lt fit

end Hierarchy.ProtocolRAM.SiteControls
end

end OAI
