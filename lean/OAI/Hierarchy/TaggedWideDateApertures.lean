import OAI.Hierarchy.TaggedWidePeerRoom

namespace OAI
/-! # Numerical pre/post aperture operands read from the three original chronological shelves -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM DescriptorExpr
open ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles WireTelescope NamedAperture Tagged PassiveWindow
open ProbeStage.ReportSockets AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM DatedRoleSheets
open scoped Classical Fin.CommRing BigOperators
variable {h W k attempts N native cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
local notation "sites" => siteLast h (2^W) k+1
local notation "degreeSlots" => stride k S.degree attempts
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
local notation "row" => columns (D:=degreeSlots) n start sites bits table here

include bounded shape published one wide wordRoom bankRoom atSite idFits siteFits in
/-- An archived nonempty local slot reads its true chronological raw ordinal
and its opposite site. Numerical vacancies have exactly width zero. -/
theorem dated_columns :
    (∀a : EndsAt ends qty s,
      ((row (slot a)).ordinal.eval m reg).val=id a.val.val.1 ∧
      ((row (slot a)).opposite.eval m reg).val=(PacketNeighbor.other (byRow ends qty s a)).val ∧
      ((row (slot a)).width.eval m reg).val=qty a.val.val.1) ∧
    (∀q,q∉Set.range slot→((row q).width.eval m reg).val=0) := by
  have rd:=neighbors S π depth mark unique rows n start bits s qty id bounded shape m published table here reg one
    wide wordRoom bankRoom atSite
  constructor
  · intro a
    have own:=(seat_value ends qty s bounded slot shape a).1
    have amount:=(seat_value ends qty s bounded slot shape a).2.1
    have pos:=a.property
    have ir:=page_read (bank n start (sites*degreeSlots) bits 1) table here m reg s (slot a) atSite wordRoom bankRoom
    have stored := published 1 (finProdFinEquiv (s,slot a))
    have read := ir.trans stored
    have addr : (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S) (port a.val.val)=
        finProdFinEquiv (s,slot a) :=
      PacketNeighbor.local_addr ends qty port (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)
        (named_coordinate S π depth mark unique rows) s a
    rw [←addr,RoleWidths.shelf_live] at read
    have ord : (row (slot a)).ordinal.eval m reg=(id a.val.val.1:Word native) := by
      simpa [columns,DatedRoleSheets.role,RoleField.data,Nat.ne_of_gt pos] using read
    have other:=rd.siteAt (slot a) _ own (by rw [amount];exact pos)
    have w:=rd.widthAt (slot a)
    simp only [PacketNeighbor.amount,own,Option.elim_some,amount] at w
    exact ⟨by rw [ord,Fin.val_cast_of_lt (idFits _)],
      by change ((pageRead _ _ _ _).eval _ _).val=_;rw [other,Fin.val_cast_of_lt ((PacketNeighbor.other _).isLt.trans_le siteFits)],
      by change ((pageRead _ _ _ _).eval _ _).val=_; rw [w,Fin.val_cast_of_lt (wide _)]⟩
  · intro q missing
    have own:=(seat_vacant ends qty s bounded slot shape q missing).1
    have w:=rd.widthAt q
    change ((pageRead _ _ _ _).eval _ _).val=_
    simp only [w,PacketNeighbor.amount,own,Option.elim_none,Nat.cast_zero,Fin.val_zero]

open private Overlap.minimum from OAI.Hierarchy.TaggedWideOverlapNative in
include published one wide wordRoom bankRoom atSite order idFits siteFits in
/-- Every datum needed by the stable compactor and interval rebaser. The
start uses increasing original identifiers even among parallel records. -/
theorem dated_apertures (capFit : cap<2^native) (room : ∀p : (portGraph sites).Port s,total p.val.1<2^native) :
    (∀i,(common row i).eval m reg=((parts).base i:Word native)) ∧
    (∀i,(row i).width.eval m reg=((parts).width i:Word native)) ∧
    (∀i q,(aperture cap row (.inl (i,q))).eval m reg=((ChordAperture.sizeAt parts i q).val:Word native)) ∧
    (∀i b,(aperture cap row (.inr (.inl (i,b)))).eval m reg=((ChordAperture.head parts i b).val:Word native)) ∧
    (∀q,(aperture cap row (.inr (.inr q))).eval m reg=(ChordAperture.room parts q:Word native)) := by
  have rd:=neighbors S π depth mark unique rows n start bits s qty id bounded shape m published table here reg one
    wide wordRoom bankRoom atSite
  have observed:=dated_columns S π depth mark unique rows n start bits s qty id bounded shape m published table here reg
    one wide wordRoom bankRoom atSite idFits siteFits
  have vac (i) (no : (parts).owner i=none) : (parts).width i=0 := by
    by_cases h:i∈Set.range slot
    · obtain ⟨a,rfl⟩:=h
      rw [(seat_value ends qty s bounded slot shape a).1] at no
      contradiction
    · exact (seat_vacant ends qty s bounded slot shape i h).2.1
  have c (i) : (common row i).eval m reg=((parts).base i:Word native) := by
    by_cases hi:i∈Set.range slot
    · obtain ⟨a,rfl⟩:=hi
      rw [(seat_value ends qty s bounded slot shape a).2.2]
      exact common_live ends qty s slot id order row m reg siteFits wide observed.1 observed.2 a
    · obtain ⟨own,w,start⟩:=seat_vacant ends qty s bounded slot shape i hi
      have z : (row i).width.eval m reg=0 := Fin.ext (observed.2 i hi)
      simp [common,active,Expr.eval,Comparison.test,z,start]
  have w (i) : (row i).width.eval m reg=((parts).width i:Word native) := by
    have a:=rd.widthAt i
    change (pageRead _ _ _ _).eval _ _=_
    rw [a]
    cases own:(parts).owner i with
    | none=>simp [PacketNeighbor.amount,own,vac i own]
    | some p=>simp [PacketNeighbor.amount,own]
  have weights:=weight_read parts row m reg rd siteFits (seat_owned ends qty s bounded slot shape) vac
  refine ⟨c,w,weights,?_,?_⟩
  · intro i b
    cases b
    · rfl
    · have bound : (parts).base i<2^native := by
        by_cases hi:i∈Set.range slot
        · obtain ⟨a,rfl⟩:=hi
          exact (Nat.le_add_right _ _).trans_lt (((parts).top _ _ (seat_value ends qty s bounded slot shape a).1).trans_lt (room _))
        · rw [(seat_vacant ends qty s bounded slot shape i hi).2.2];exact Nat.two_pow_pos _
      apply Fin.ext
      change ((Overlap.small (.lit cap) (common row i)).eval m reg).val=
        ((min cap ((parts).base i):ℕ):Word native).val
      rw [Overlap.minimum,c,Fin.val_cast_of_lt bound,
        Fin.val_cast_of_lt ((Nat.min_le_left cap ((parts).base i)).trans_lt capFit)]
      change min ((cap:Word native).val) ((parts).base i)=min cap ((parts).base i)
      rw [Fin.val_cast_of_lt capFit]
  · intro q
    simp only [aperture,LocalPrefix.total_eval,weights,←Nat.cast_sum,size_sum ends qty s bounded slot shape]

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
