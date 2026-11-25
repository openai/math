import OAI.Hierarchy.DescentTerminalPreflightChronology
import OAI.Hierarchy.DescentTerminalPreflightPorts
import OAI.Hierarchy.DescentTerminalCableWidthReport
import OAI.Hierarchy.DescentTerminalPublicWidthTape
import OAI.Hierarchy.DescentTerminalSocketWidths

import OAI.Hierarchy.DescentTerminalPreflightBook

namespace OAI
/-! # Earlier book, roster and width words at the actual draft date -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalHeaderDraft DescentTerminalLocalPortBook
open DescentTerminalDenseHeader DescentTerminalDenseHeaderBoot DescentTerminalWidthRowsRAM
open DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns DescentTerminalHeaderGroups
open DescentTerminalGrainProfiles DescentTerminalPaidHeaderEvents DescentKernelHistory
open Computability.BorderVNP.Crossing DescentTerminalRecipeRows DescentTerminalBinPack DescentSortedRoster
open ThreeFlat.Routing ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable (x : Spec) (base q p : ℕ) (peer : Bank) (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ) {w : ℕ} (bookMem : Memory w) (values : ℕ→ℕ)
    (paid act : Fin x.scalar.blocks→Bank) (boot : x.Before base paid act old peer total modulo homes boundary)
    (room : x.maskBase base<2^w) (positive : 0<x.strips)
local notation "H" => x.scalar.shops
local notation "L_" => x.eventInputs base peer old
local notation "A_" => x.draft base total modulo homes boundary
local notation "T_" => x.cables base peer old
local notation "U_" => x.publicWidths base
local notation "controlled" => (x.controls base).after values (Book.expression (x.parts base)) bookMem
local notation "cabled" => (T_).final q p controlled
local notation "published" => x.afterWidths base q p peer old controlled
local notation "draftIn" => litMem (x.literalBase base) x.paidRows published

private theorem bank_frame {bound : ℕ} {m m' : Memory w} (frame : ∀i<bound,m' i=m i)
    (b : Bank) (fits : b.base+b.size≤bound) (i : Computability.VPVNP.BurstRAM.Word w) : b.read m' i=b.read m i := by
  have off:=Nat.mod_lt i.val (show 0<b.size from Nat.two_pow_pos _)
  exact frame (b.base+i.val%b.size) (by omega)

private theorem prefix_bound (L : DescentTerminalWidthRowsRAM.Layout) :
    L.prefix.base+L.prefix.size ≤ L.stop ∧ L.output.base+L.output.size ≤ L.stop := by
  change _ ≤ L.prefix.base+L.prefix.size+L.output.size+1+L.groups+L.groups ∧
    L.prefix.base+L.prefix.size+L.output.size ≤ L.prefix.base+L.prefix.size+L.output.size+1+L.groups+L.groups
  omega

include boot room positive
/-- These are the four actual lower-memory frames. In particular the private prefix
exists before the public scan and the public prefix exists before the literal writes. -/
theorem port_dates :
    (∀i<x.bookEnd base,controlled i=bookMem i) ∧
    (∀i<(x.controls base).finish,cabled i=controlled i) ∧
    (∀i<x.cableEnd base,published i=cabled i) ∧
    (∀i<x.literalBase base,draftIn i=published i) := by
  obtain ⟨_,_,_,_,_,high,_,_,lit⟩:=x.all_lower base room
  have a:=(x.controls base).any bookMem values _ (x.control_fits base room positive) high
  have b:=(T_).run q p controlled (x.fits_cables base room paid act old peer total modulo homes boundary boot)
  have c:=x.after_public base room
  have d:=lit_install (x.literalBase base) x.paidRows published lit
  exact ⟨fun i hi=>a.2.2 i (.inl hi),b.2.2.2,(U_).before q p cabled c.2,fun i hi=>d.2.2.2 i (.inl hi)⟩

theorem book_at_ports {G V M A a : ℕ} (t : Fin H→Book G V M A a) (W : ℕ)
    (issued : Book.Issued (x.parts base) t bookMem)
    (totals : ∀i : Fin (Book.Bytes G V M A a),total.read bookMem (i.val : Computability.VPVNP.BurstRAM.Word w)=countTable q i)
    (bounds : ∀i : Fin (x.paidRows+1),bookMem (boundary+i.val)=
      (DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val]) :
    Book.Issued (x.parts base) t draftIn ∧
    (∀i : Fin (Book.Bytes G V M A a),total.read draftIn (i.val : Computability.VPVNP.BurstRAM.Word w)=countTable q i) ∧
    (∀i : Fin (x.paidRows+1),draftIn (boundary+i.val)=
      (DescentTerminalBinPackCheap.boundaries w W x.paidRows)[i.val]) := by
  obtain ⟨u,v,s,t'⟩:=x.port_dates base q p peer old total modulo homes boundary bookMem values paid act boot room positive
  obtain ⟨e,f,g,h,k,l,m,_,_⟩:=x.layers base
  have all (i : ℕ) (lo : i<x.bookEnd base) : draftIn i=bookMem i :=
    (t' i (by omega)).trans ((s i (by omega)).trans ((v i (by omega)).trans (u i lo)))
  have rc:=boot.total
  have bc:=boot.boundary
  exact ⟨⟨fun i j=>(bank_frame all _ (x.book_banks base j).1 _).trans (issued.source i j),
    fun j i=>(bank_frame all _ ((x.book_banks base j).2.trans h) _).trans (issued.values j i)⟩,
    fun i=>(bank_frame all total (by omega) _).trans (totals i),
    fun i=>(all _ (by have:=i.isLt;omega)).trans (bounds i)⟩

section Counts
variable {deg : ℕ} {P : Type} [Fintype P] {bw : P→ℕ} (N : Network deg P bw) (home : N.Site→Fin x.scalar.shops)
    (R : Fin x.scalar.shops→Fin x.degree→Option (Fin x.scalar.shops)) (rom : ℕ)
    (privateOut publicOut : Fin 4→Bank) (privateTape publicTape : List (Profile q p))
local notation "pc" => fun i=>DescentTerminalExteriorHeaders.siteMass N home i/p
local notation "cc" => slotCount (p:=p) R N home
local notation "layout_" => DescentTerminalDenseHeaderBoot.layout q p rom
local notation "private_" => layout_ (T_).printer.output (privateOut 0) (privateOut 1) (privateOut 2) (privateOut 3)
local notation "public_" => layout_ (U_).widthLayout.output (publicOut 0) (publicOut 1) (publicOut 2) (publicOut 3)
local notation "reads_" => DescentTerminalDenseHeaderRAM.Reads

/-- The cable premises are the two preceding outputs of Counter.cable_fields. The
public stream and its inclusive prefix are computed here from the earlier cohort
census, including zero-volume hosts. Both use the common mounted four-table ROM. -/
theorem port_frames (hpq : 0<q*p) (romEnd : rom+extent q p≤x.bookEnd base)
    (tables : ∀j<extent q p,bookMem (rom+j)=back w q p j)
    (sockets : H*x.degree≤peer.size)
    (roster : ∀(i : Fin H) (j : Fin x.degree),bookMem (peer.base+(i.val*x.degree+j.val))=
      (DescentPackedColony.target (R i j):Computability.VPVNP.BurstRAM.Word w))
    (counts : Fin H→ℕ) (cap : ∀i,counts i≤(U_).maxCohorts)
    (census : ∀i : Fin H,bookMem ((U_).old.base+i.val)=(counts i : Computability.VPVNP.BurstRAM.Word w))
    (publicMass : ∀i,counts i*(U_).rate=pc i)
    (tapeEq : tape q p pc=publicTape) (rows : publicTape.length≤x.headerRows)
    (cableWords : reads_ private_ (padded (n:=x.headerRows) privateTape) cabled)
    (cablePrefix : ∀j : Fin (H*x.degree),(T_).printer.prefix.read cabled (j.val:Computability.VPVNP.BurstRAM.Word w)=
      ((passed q p cc (j.val+1)).length:Computability.VPVNP.BurstRAM.Word w)) :
    Earlier (p:=p) (q:=q) A_ L_ R N home draftIn ∧
      reads_ private_ (padded (n:=x.headerRows) privateTape) published ∧
      reads_ public_ (padded (n:=x.headerRows) publicTape) published := by
  obtain ⟨ctl,wire,pub,draft⟩:=x.port_dates base q p peer old total modulo homes boundary bookMem values paid act boot room positive
  obtain ⟨e,f,g,h,k,l,m,s,_⟩:=x.layers base
  obtain ⟨high,_,_,_,_,_,_,_,_⟩:=x.all_lower base room
  have oldFrame (i : ℕ) (u : i<x.bookEnd base) : cabled i=bookMem i :=
    (wire i (u.trans_le k)).trans (ctl i u)
  have peerEnd:=boot.roster
  have cend:=(prefix_bound (T_).printer).1
  have outEnd:=(prefix_bound (T_).printer).2
  have pend:=(prefix_bound (U_).widthLayout).1
  change (T_).printer.prefix.base+(T_).printer.prefix.size≤x.cableEnd base at cend
  change (T_).printer.output.base+(T_).printer.output.size≤x.cableEnd base at outEnd
  change (U_).widthLayout.prefix.base+(U_).widthLayout.prefix.size≤x.literalBase base at pend
  have pubFit:=x.after_public base room
  have cfit:=(U_).scale_space pubFit.2
  have oldRoom : H≤(U_).old.size := Nat.le_pow_clog (by decide) _
  have ce:=x.census_end base
  have input (i : Fin H) : cabled ((U_).old.base+i.val)=(counts i : Computability.VPVNP.BurstRAM.Word w) := by
    have within:=i.isLt.trans_le oldRoom
    change (U_).old.base+(U_).old.size≤x.cohortEnd base at ce
    exact (oldFrame _ (by omega)).trans (census i)
  have source := DescentTerminalPublicCountRAM.count_read (U_).base (U_).maxCohorts H (U_).old (U_).rate
    cabled pubFit.1 cfit counts cap oldRoom input
  have eq : (fun i=>counts i*(U_).rate)=pc := funext publicMass
  have length : (tape q p (fun i=>counts i*(U_).rate)).length≤x.headerRows := by rw [eq,tapeEq];exact rows
  have publicReads:=(U_).exterior q p cabled pubFit.1 pubFit.2 counts cap oldRoom input length hpq
    rom (publicOut 0) (publicOut 1) (publicOut 2) (publicOut 3) (by omega : rom+extent q p≤x.cableEnd base)
    (fun j hj=>(oldFrame _ (by omega)).trans (tables j hj))
  have wordTape : tape q p (fun i => counts i*(U_).rate) = publicTape :=
    (congrArg (tape q p) eq).trans tapeEq
  have outputWords : reads_ public_ (padded (n:=x.headerRows) publicTape) published :=
    (congrArg (fun cells => reads_ public_ (padded (n:=x.headerRows) cells) published) wordTape).mp publicReads
  refine ⟨⟨?_,?_,?_,?_⟩,?_,outputWords⟩
  · intro b hb
    rcases List.mem_cons.mp hb with here|hb
    · rw [here]
      change peer.base+peer.size≤x.draftBase base;omega
    rcases List.mem_cons.mp hb with here|hb
    · rw [here]
      change (T_).printer.prefix.base+(T_).printer.prefix.size≤x.draftBase base;omega
    rw [List.mem_singleton.mp hb]
    exact pend.trans s
  · intro i j
    have inRange : i.val < H := i.isLt
    have ix : i.val*x.degree+j.val<H*x.degree :=
      (Nat.add_lt_add_left j.isLt _).trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right x.degree inRange)
    have peerFit : peer.Fits w (x.cohortEnd base) :=
      ⟨Nat.two_pow_pos _,by omega,peerEnd⟩
    rw [show (L_).roster=peer from rfl,DescentPackedZip.bank_read peer draftIn (ix.trans_le sockets) peerFit]
    exact (draft _ (by omega)).trans ((pub _ (by omega)).trans ((oldFrame _ (by omega)).trans (roster i j)))
  · intro j
    exact (bank_frame draft _ (cend.trans m) _).trans ((bank_frame pub _ cend _).trans (cablePrefix j))
  · intro j
    have z:=DescentTerminalHeaderSockets.prefix_reads ((U_).scaled cabled) (U_).widthLayout q p
      (fun i=>counts i*(U_).rate) (fun i=>Nat.mul_le_mul_right _ (cap i)) length
      (DescentTerminalPublicCountRAM.bank_fits (U_).base (U_).maxCohorts H cfit)
      (Nat.le_pow_clog (by decide) _) pubFit.2 source j
    have massEq := congrArg (fun amounts : Fin x.scalar.shops → ℕ =>
      ((passed q p amounts (j.val+1)).length : Computability.VPVNP.BurstRAM.Word w)) eq
    exact (bank_frame draft _ pend _).trans (z.trans massEq)
  · apply five_reads cableWords
    have bound:=source_ends q p rom (T_).printer.output outEnd (romEnd.trans (k.trans l))
    intro j val
    exact bank_frame pub _ (bound j) val

end Counts
end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
