import OAI.Hierarchy.DescentContactCatalog

namespace OAI
/-! # Original and width-converted operands after the contact output mounts -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (first : ℕ) {H G a w : ℕ}
local notation "batchSize" => A.donor.batch
local notation "f" => A.donor.fieldBits
local notation "t" => A.metaBits
local notation "v" => A.donor.cargoBits
local notation "P" => A.marker first
local notation "B" => A.flagPage first
local notation "J" => A.countPage first
local notation "K" => A.haloPage first
local notation "U" => A.choicePage first
local notation "E" => A.projected first

abbrev PresentAt (floor : ℕ) (m : Memory w) (op : Expr) (x : Fin H→Fin G→Cell a) :=
  op.Fits w floor ∧ Source op x batchSize m

structure Casts (m dst : Memory w) : Prop where
  raw {H G a : ℕ} (op : Expr) (x : Fin H→Fin G→Cell a) (prior : A.PresentAt P m op x) : A.PresentAt U dst op x
  shape {H G : ℕ} (op : Expr) (x : Fin H→Fin G→Cell A.markerBits) (prior : A.PresentAt P m op x) :
    A.PresentAt U dst (DescentContactMarkerShape.port A.shapes A.markerBits t batchSize P op)
      (fun h g=>DescentContactMarkerShape.shape A.shapes A.markerBits t (x h g) 0)
  flag {H G : ℕ} (op : Expr) (x : Fin H→Fin G→Cell A.markerBits) (prior : A.PresentAt P m op x) :
    A.PresentAt U dst (DescentStaticUnary.query (DescentContactMarkerShape.flag A.markerBits f) batchSize B op)
      (fun h g=>DescentContactMarkerShape.flag A.markerBits f (x h g) 0)
  count {H G : ℕ} (op : Expr) (x : Fin H→Fin G→Cell f) (prior : A.PresentAt P m op x) :
    A.PresentAt U dst (DescentContactWidthPage.expr J f t batchSize op) (fun h g=>DescentContactWidthPage.recode t (x h g))
  halo {H G : ℕ} (op : Expr) (x : Fin H→Fin G→Cell v) (prior : A.PresentAt P m op x) :
    A.PresentAt U dst (DescentContactWidthPage.expr K v t batchSize op) (fun h g=>DescentContactWidthPage.recode t (x h g))

private theorem transport {floor top : ℕ} {old dst : Memory w} {op : Expr} {x : Fin H→Fin G→Cell a}
    (ready : A.PresentAt floor old op x) (before : floor≤top) (kept : ∀j,j<floor→dst j=old j) :
    A.PresentAt top dst op x :=
  ⟨ProtocolRAMGeneratedWrite.fits_mono op before ready.1,fun q=>
    (ProtocolRAM.eval_below op _ old dst ready.1 kept).trans (ready.2 q)⟩

/-- All input expressions stay in the original projected RAM throughout the four page
mounts. Each lookup consults its actual immutable mounted page. -/
theorem casts (m : Memory w) (room : U<2^w) : A.Casts first m (A.halos first m) :=by
  have pb : P≤B:=Nat.le_add_right ..
  have bj : B≤J:=Nat.le_add_right ..
  have jk : J≤K:=Nat.le_add_right ..
  have ku : K≤U:=Nat.le_add_right ..
  have mark:=DescentContactMarkerShape.any A.shapes A.markerBits t batchSize P m ((bj.trans (jk.trans ku)).trans_lt room)
  have flags:=ROM.frame A.flagPages (A.markerBits*batchSize) B (A.marked first m)
  have counts:=DescentContactWidthPage.any J f t batchSize (A.flagged first m) (ku.trans_lt room)
  have halos:=DescentContactWidthPage.any K v t batchSize (A.counts first m) room
  have firstKept j (h:j<P) : A.marked first m j=m j:=mark.2.2 j (.inl h)
  have secondKept j (h:j<B) : A.flagged first m j=A.marked first m j:=flags j (.inl h)
  have thirdKept j (h:j<J) : A.counts first m j=A.flagged first m j:=counts.2.2 j (.inl h)
  have finalKept j (h:j<K) : A.halos first m j=A.counts first m j:=halos.2.2 j (.inl h)
  constructor
  · intro H G b op x previous
    exact transport A (transport A (transport A (transport A previous pb firstKept) bj secondKept) jk thirdKept) ku finalKept
  · intro H G op x previous
    have ob:=(DescentContactMarkerShape.read A.shapes A.markerBits t P m
      ((bj.trans (jk.trans ku)).trans_lt room)).2.1 op x previous.1 previous.2
    exact transport A (transport A (transport A ob bj secondKept) jk thirdKept) ku finalKept
  · intro H G op x previous
    have saved:=transport A previous pb firstKept
    have page:=DescentStaticUnary.read (H:=H) (G:=G) (M:=batchSize) (DescentContactMarkerShape.flag A.markerBits f)
      (by simp [DescentContactMarkerShape.flag]) B (A.marked first m) ((jk.trans ku).trans_lt room)
    have seen:=page.2.1 op x saved.1 saved.2
    exact transport A (transport A seen jk thirdKept) ku finalKept
  · intro H G op x previous
    have saved:=transport A (transport A previous pb firstKept) bj secondKept
    exact transport A ⟨DescentContactWidthPage.fits J f t batchSize op saved.1 (ku.trans_lt room),
      DescentContactWidthPage.posted J f t batchSize _ (ku.trans_lt room) op x saved.1 saved.2⟩ ku finalKept
  · intro H G op x previous
    have saved:=transport A (transport A (transport A previous pb firstKept) bj secondKept) jk thirdKept
    exact ⟨DescentContactWidthPage.fits K v t batchSize op saved.1 room,
      DescentContactWidthPage.posted K v t batchSize _ room op x saved.1 saved.2⟩

theorem catalog_casts (m : Memory w) (room : E<2^w) : A.Casts first m (A.catalogImage first m) :=by
  have back:=A.casts first m ((Nat.le_add_right ..).trans_lt room)
  have frames j (h:j<U) : A.catalogImage first m j=A.halos first m j:=
    ROM.frame A.labels A.choiceBits U (A.halos first m) j (.inl h)
  exact ⟨fun op x src=>transport A (back.raw op x src) le_rfl frames,
    fun op x src=>transport A (back.shape op x src) le_rfl frames,
    fun op x src=>transport A (back.flag op x src) le_rfl frames,
    fun op x src=>transport A (back.count op x src) le_rfl frames,
    fun op x src=>transport A (back.halo op x src) le_rfl frames⟩

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
