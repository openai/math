import OAI.Hierarchy.ProtocolRAMFrozenFormat

namespace OAI
/-! # Running a complete format in its own forward-allocated physical RAM window -/
noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr PhysicalProcedure
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterGroups TaggedShorterReportedPublish
open TaggedShorterReportAdvice ProtocolRAMTranslatedKey ProtocolRAMPackedRanked ProtocolRAMFrozenWidthFrame
open scoped Fin.CommRing Classical

structure Format.InputWords (f : Format) {W : ℕ} (r : ℕ) (a : Inputs) (old : Fin f.N→ProtocolRAMEmit.Row) (m : Memory W) : Prop where
  width : ∀i : Fin f.N,a.width.read m ((3*i.val:ℕ):Word W)=((old i).width:Word W)
  bias : ∀z : Word W,a.bias.read m z=(((z.val%(2^f.gb))*(f.menu+1):ℕ):Word W)
  classes : ∀i : Fin f.N,a.classes.read m ((old i).width:Word W)=((classOf old f.w f.menu i).val:Word W)
  copies : ∀i : Fin f.N,a.weights.read m ((old i).width:Word W)=(pieces old f.w i:Word W)
  tables : ∀j : Fin 13,∀x : ℕ,x<2^f.bits → (bank f.rom f.bits j).read m (x:Word W)=
    words f.groups f.D f.B f.M (f.window.base r) f.w f.menu f.cap j x
  origins : ∀g : Fin f.groups,a.origins.read m (g.val:Word W)=((f.window.widthBase r+2*g.val*f.D:ℕ):Word W)

structure Format.Limits (f : Format) (W : ℕ) (old : Fin f.N→ProtocolRAMEmit.Row) : Prop where
  groups : f.groups≤2^f.gb
  groupWords : 2^f.gb≤2^W
  order : StrictMono (fun i=>(old i).link)
  copyBound : ∀i,pieces old f.w i≤f.cap
  groupCap : f.groups≤2^f.bits
  boundCap : f.D≤2^f.bits
  mapCap : f.groups*poolBatchCount f.D f.B≤2^f.bits
  tableCap : 10*(f.N*f.cap)≤2^f.bits
  widthFit : ∀i,(old i).width<2^f.bits
  wide : 2^f.bits≤2^W
  menuFits : f.menu<2^W
  typeFits : f.γ≤f.menu
  small : 10≤2^W
  slotFits : f.cap<2^W
  batch : 0<f.B
  idFits : f.B≤2^f.n
  batchFits : f.B≤2^W

theorem Format.run (f : Format) (W r : ℕ) (a : Inputs) (old : Fin f.N→ProtocolRAMEmit.Row) (m : Memory W)
    (ready : f.Ready W r a) (data : f.InputWords r a old m) (limits : f.Limits W old)
    (groupFit : ∀i,0<pieces old f.w i → (f.rows a m old i).group<f.groups)
    (bound : ∀g : Fin f.groups,size (f.rows a m old) f.w f.menu f.γ g≤f.D)
    (pl : ∀g : Fin f.groups,Bool → Fin (size (f.rows a m old) f.w f.menu f.γ g) ↪ Fin f.D)
    (located : ∀s (g : Fin f.groups) (u : ProtocolRAMReportedPorts.Unit (f.rows a m old) f.w f.menu f.γ g.val),
      (pl g s (common (f.rows a m old) f.w f.menu f.γ g.val limits.order.injective u)).val=
        f.starts a m s u.1.val+u.2.val) :
    let s := f.window
    let addr := TaggedShorterScatter.layout s.C f.D (s.base r) (s.boardFit r W ready.room)
    let counts := size (groups:=f.groups) (f.rows a m old) f.w f.menu f.γ
    ∃ out,(f.phase W r a).Exec m out (f.clock r a) ∧
      (∀x : TaggedShorterSlotWidth.Slot f.groups f.D,out (TaggedShorterSlotWidth.index (s.widthBase r) x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth (f.rows a m old) f.w f.menu f.γ limits.order.injective) x:Word W)) ∧
      (∀x : TaggedShorterScatter.Field s.C f.D,out (addr x).val=
        (TaggedShorterScatter.contents counts bound limits.batch limits.idFits pl x:Word W)) ∧
      ∀u,u<r → out u=m u := by
  intro s addr counts
  let L := s.rank r
  let R := f.rows a m old
  let lr := f.starts a m
  obtain ⟨anch,first,groupRead,slotRead,unchanged⟩ := f.anchors W r a ready m old
  have lower (c : Bank) (bound : c.Fits W r) (i : Word W) : c.read anch i=c.read m i :=
    unchanged _ ((Nat.add_lt_add_left (Nat.mod_lt i.val bound.1) _).trans_le bound.2.2)
  have fits (c : Bank) (h : c∈[a.directory,a.offset,a.left,a.right,a.width,a.bias,a.classes,a.weights,a.origins]) :=
    ready.inputs c h
  have oldW := fits a.width (by simp)
  have bias := fits a.bias (by simp)
  have classes := fits a.classes (by simp)
  have weights := fits a.weights (by simp)
  have origins := fits a.origins (by simp)
  have low (c : Bank) (hc : c.Fits W r) := s.low_fits r W c hc
  have tf := s.rank_fits r W ready.room
  have hi := s.base_stop r
  have start := s.r_base r
  have rankSafe := s.rank_safe r
  have wh : s.stop r < 2^W := ready.room
  have mkFit (c : Bank) (e : Safe c (s.base r) r) : c.Fits W (s.base r) :=
    ⟨Nat.two_pow_pos _, (Nat.le_add_left c.size c.base).trans_lt
      (e.below.trans_lt (hi.trans_lt wh)), e.below⟩
  have widen (c : Bank) (hc : c.Fits W (s.base r)) (limit : ℕ) (h : s.base r≤limit) : c.Fits W limit :=
    ⟨hc.1,hc.2.1,hc.2.2.trans h⟩
  have pROM (j : Fin 13) := s.low_safe r W _ (ready.publicROM j)
  have saveW := s.low_safe r W _ oldW
  have saveO := s.low_safe r W _ origins
  have saveLeft := s.anchor_safe r W ready.room 1
  have saveRight := s.anchor_safe r W ready.room 3
  have bf : (TaggedShorterEmitMachine.term (f.tables r a) f.γ r).Fits W (s.base r) :=
    term_fits f.rom f.bits (s.base r) f.γ r a.width L.group L.rank (s.anchor r 1) (s.anchor r 3)
      (fun j=>mkFit _ (pROM j)) (mkFit _ saveW) (mkFit _ rankSafe.1) (mkFit _ rankSafe.2)
      (mkFit _ saveLeft) (mkFit _ saveRight)
  have wb : s.base r≤ s.widthBase r := Nat.le_add_right _ _
  have ws : s.widthBase r≤ s.src r := Nat.le_add_right _ _
  have ss : s.src r≤ s.widthSrc r := Nat.le_add_right _ _
  have wf (c : Bank) (hc : Safe c (s.base r) r) :=
    widen c (mkFit c hc) (s.widthBase r) wb
  have pf : (TaggedShorterSlotWidth.term (f.tables r a) a.origins f.D f.γ (r+1)).Fits W (s.widthBase r) :=
    width_term_fits f.rom f.bits (s.widthBase r) f.D f.γ (r+1) a.width L.group L.rank (s.anchor r 1) (s.anchor r 3)
      a.origins (fun j=>wf _ (pROM j)) (wf _ saveW) (wf _ rankSafe.1) (wf _ rankSafe.2)
      (wf _ saveLeft) (wf _ saveRight) (wf _ saveO)
  have tapeFit : s.widthSrc r+s.tape<2^W := ready.room
  have srcFit : s.src r+s.tape<2^W := by change s.widthSrc r<2^W;omega
  obtain ⟨out,rest,widthRead,_,_,_,fields,preserve⟩ := ProtocolRAMPackedFinal.publish_stored
    (groups:=f.groups) (D:=f.D) (B:=f.B) (M:=f.M) (n:=f.n) (w:=f.w) (menu:=f.menu)
    (cap:=f.cap) (rom:=f.rom) (bits:=f.bits) (base:=s.base r) (src:=s.src r) (sink:=r) (γ:=f.γ) (gb:=f.gb)
    L a.width (s.anchor r 2) a.bias a.classes a.weights (s.anchor r 1) (s.anchor r 3) R lr anch tf
    (low _ oldW) (s.anchor_fits r W ready.room 2) (low _ bias) (low _ classes) (low _ weights)
    (s.anchor_fits r W ready.room 1) (s.anchor_fits r W ready.room 3)
    (fun i=>(lower _ oldW _).trans (data.width i)) groupRead
    (fun z=>(lower _ bias _).trans (data.bias z)) (fun i=>(lower _ classes _).trans (data.classes i))
    (fun i=>(lower _ weights _).trans (data.copies i)) (slotRead false) (slotRead true)
    limits.groups limits.groupWords limits.order (fun j=>low _ (ready.publicROM j))
    (fun j x hx=>(lower _ (ready.publicROM j) _).trans (data.tables j x hx)) groupFit limits.order.injective
    bound limits.copyBound pl located limits.groupCap limits.boundCap limits.mapCap limits.tableCap limits.widthFit
    limits.wide limits.menuFits limits.typeFits limits.small limits.slotFits limits.batch limits.idFits limits.batchFits
    (s.boardFit r W ready.room) ws srcFit (by omega) (s.sinkApart r W ready.room)
    (ProtocolRAMGeneratedWrite.fits_mono _ (wb.trans ws) bf) bf
    (s.widthBase r) (s.widthSrc r) (r+1) a.origins (low _ origins)
    (fun g=>(lower _ origins _).trans (data.origins g)) saveW rankSafe.1 rankSafe.2 saveLeft saveRight saveO pROM
    le_rfl ss tapeFit (by omega) (s.widthApart r)
    (ProtocolRAMGeneratedWrite.fits_mono _ (ws.trans ss) pf) pf
  refine ⟨out,?_,widthRead,fields,?_⟩
  · intro P Q K mach pc reg pub exit install words cfg raw entry same
    exact Procedure.Exec.then first rest mach pc reg pub exit install words cfg raw entry same
  · intro t ht
    have safe:=s.before r t ht
    exact (preserve t safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2).trans (unchanged t ht)

end Hierarchy.ProtocolRAMFrozenWindow

end
end OAI
