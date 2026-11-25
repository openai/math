import OAI.Hierarchy.DescentTerminalHeaderDraft
import OAI.Hierarchy.DescentTerminalPaidHeaderOffsets

namespace OAI
/-! # Physical paid-event fields for each reached two-ended port group -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalSpanBook
open DescentTerminalChipSource DescentTerminalGrainProfiles DescentTerminalCableOrder DescentTerminalWidthRowsRAM
open DescentSortedRoster Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open scoped Classical Fin.CommRing BigOperators
noncomputable section

private theorem sameMode {a b : Prop} [Decidable a] [Decidable b] (equiv : a ↔ b) :
    (if a then 1 else 0 : ℕ) = (if b then 1 else 0) := by
  by_cases hit : a
  · simp only [ite_eq_left hit,ite_eq_left (equiv.mp hit)]
  · simp only [ite_eq_right hit,ite_eq_right (fun hb=>hit (equiv.mpr hb))]

private theorem monotoneRows {k:ℕ} (q p:ℕ) (c:Fin k→ℕ) :
    Monotone (fun a=>(passed q p c a).length) := by
  apply monotone_nat_of_le_succ
  intro a
  by_cases live:a<k
  · let i : Fin k := ⟨a,live⟩
    exact (Nat.le_add_right (passed q p c a).length (poolBatchCount (c i) q)).trans_eq
      (passed_len q p c i).symm
  · have done: (List.ofFn c).length≤a:=by simpa using Nat.le_of_not_gt live
    simp [passed,List.take_of_length_le done,List.take_of_length_le (done.trans (Nat.le_succ _))]

variable (A:Arena) {deg D p q W K w:ℕ} (L:DescentTerminalHeaderSockets.Layout) (R:Fin A.sites→Fin D→Option (Fin A.sites))
    {P Tag:Type} [Fintype P] {bw:P→ℕ} (N:Network deg P bw) (home:N.Site→Fin A.sites)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hp:0<p) (hq:0<q) (edges:∀e,p∣N.width e) (ports:∀z,p∣bw z)
    (sorted:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))
    (r:∀v,DescentKernelHistory.Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (birth:∀v,(r v).Node↪ℕ)
local notation "G" => order N home native p ext nodes ops
local notation "sites" => DescentTerminalBundleRows.site G r hp birth
local notation "cut" => cableOffset (p:=p) R N home q
local notation "pub" => publicOffset (p:=p) N home q
local notation "cc" => slotCount (p:=p) R N home
local notation "pc" => fun v=>DescentTerminalExteriorHeaders.siteMass N home v/p
local notation "event" => Slots.emitted (H:=A.sites) (q:=q) (W:=W) (K:=K) («sites»:=sites)
def expected (c:Column) (a:GroupRow (q:=q) sites) : ℕ := match c with
  | .active=>1
  | .mode=>if ((DescentTerminalGraphPositions.Order.groups G a.1).symm a.2.1).val=none then 1 else 0
  | .source=>DescentTerminalScatterRows.srcStart N home native ext nodes ops r hp birth a+a.2.2.val

variable {nG nV nM nA bits:ℕ} (m:Memory w) (ok:Room A L D w)
    (shelves:∀v,DescentTerminalLocalPortBook.Room
      (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v) nG nV nM nA)
    (labels:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).Name→Word bits)
    (refs:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).Arg→Word bits)
    (wp:0<W)
    (fit:∀v,(DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v).rows q≤W)
    (paid:purchased W (counts (q:=q) (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth))≤A.rows)
    (counter:A.rows+W<2^w) (boundary:A.boundaries+(A.rows+1)≤A.start)
    (book:Book.Issued A.parts (fun v=>issue
      (DescentTerminalBundleRows.site (order N home native p ext nodes ops) r hp birth v)
      (shelves v) (labels v) (refs v)) m)
    (countRom:∀j:Fin (Book.Bytes nG nV nM nA bits),A.countTable.read m (j.val:Word w)=countTable q j)
    (boundRom:∀j:Fin (A.rows+1),m (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
structure Earlier (m:Memory w) : Prop where
  low : ∀b∈[L.roster,L.cablePrefix,L.publicPrefix],b.base+b.size≤A.start
  roster : ∀(v:Fin A.sites) (j:Fin D),L.roster.read m ((v.val*D+j.val:ℕ):Word w)=(DescentPackedColony.target (R v j):Word w)
  cables : ∀j:Fin (A.sites*D),L.cablePrefix.read m (j.val:Word w)=(cut (j.val+1):Word w)
  exterior : ∀j:Fin A.sites,L.publicPrefix.read m (j.val:Word w)=(pub (j.val+1):Word w)

set_option maxHeartbeats 800000 in
include hq edges ports sorted covers ok wp fit paid counter boundary book countRom boundRom in
theorem published (prev:Earlier (p:=p) (q:=q) A L R N home m)
    (high:2<2^w) (hosts:A.sites<2^w) (area:A.sites*D<2^w)
    (cRoom:(tape q p cc).length<2^w) (pRoom:(tape q p pc).length<2^w)
    (length:A.rows=K*W) (c:Column) (i:Fin A.rows) :
    data A L D m (((output A).get c).base+i.val)=
      (((event wp fit (i.cast length)).elim (0:ℕ) (expected (A:=A) (q:=q) (p:=p) (N:=N) (home:=home) (native:=native) (ext:=ext) (nodes:=nodes) (ops:=ops) (r:=r) (hp:=hp) (birth:=birth) c) : ℕ) : Word w) := by
  let now_:=rowed A m
  have cursor:=cursors (W:=W) (q:=q) A L D m ok sites shelves labels refs wp fit paid counter boundary book countRom boundRom i
  have keep (b:Bank) (member:b∈[L.roster,L.cablePrefix,L.publicPrefix]) (v:Word w) : b.read now_ v=b.read m v := by
    exact row_low A L D m ok _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (prev.low _ member))
  let slots:=graphSlots R N home native ext nodes ops hp edges ports sorted covers r birth q
  have actual (v:Fin A.sites) (j:Fin (D+1)) : endAt R v cut pub j-origin R v cut pub j=slots.width v j :=
    socket_width R N home covers v j
  have small (v:Fin A.sites) (j:Fin (D+1)) : endAt R v cut pub j-origin R v cut pub j<2^w := by
    apply Nat.lt_of_le_of_lt (Nat.sub_le ..)
    refine Fin.cases ?_ (fun s=>?_) j
    · exact (within q p pc _).trans_lt pRoom
    · change DescentTerminalHeaderSockets.finish cut (ordinal R v s)<_
      cases h:ordinal R v s with
      | none=>exact Nat.two_pow_pos _
      | some a=>exact (within q p cc _).trans_lt cRoom
  have truth:=expr_read (inputs A L) R now_ high hosts area
    (fun v j=>(keep L.roster (by simp) _).trans (prev.roster v j))
    cut pub (by simp [cableOffset,passed]) (by simp [publicOffset,passed])
    (monotoneRows q p cc) (monotoneRows q p pc)
    (fun j=>(keep L.cablePrefix (by simp) _).trans (prev.cables j)) (fun j=>(keep L.publicPrefix (by simp) _).trans (prev.exterior j))
    c (resolve (q:=q) (W:=W) sites fit i.val) (by omega) small i (by simpa only [inputs,now_,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using cursor.1) cursor.2
  have locate_:=slots.locations (K:=K) (W:=W) wp fit c (origin R · cut pub) (i.cast length)
  have equals : DescentTerminalPaidHeaderEvents.result R cut pub c (resolve (q:=q) (W:=W) sites fit i.val)=
      (event wp fit (i.cast length)).elim (0:ℕ) (expected (A:=A) (q:=q) (p:=p) (N:=N) (home:=home) (native:=native) (ext:=ext) (nodes:=nodes) (ops:=ops) (r:=r) (hp:=hp) (birth:=birth) c) := by
    dsimp only [DescentTerminalPaidHeaderEvents.result,DescentTerminalPaidHeaderEvents.picked]
    simp_rw [actual]
    change (resolve (q:=q) (W:=W) sites fit (i.cast length).val).elim 0 (fun z=>number c (origin R z.1 cut pub) (locate (slots.width z.1) (List.finRange (D+1)) z.2.val))=_
    rw [locate_]
    cases h:event wp fit (i.cast length) with
    | none=>rfl
    | some z=>
      have source_:=event_source (q:=q) R N home native ext nodes ops hp hq edges ports sorted covers r birth z
      cases c with
      | active=>rfl
      | mode=>
        change (if (groupEmbed R N home native ext nodes ops hp covers z.1 z.2.1).val=0 then 1 else 0)=
          (if ((Order.groups G z.1).symm z.2.1).val=none then 1 else 0)
        exact sameMode source_.2
      | source=>exact congrArg (fun n:ℕ=>n+z.2.2.val) source_.1
  exact (issued (inputs A L) (output A) A.sites D A.rows now_ (eventRoom A L D ok) i c).trans (truth.trans (congrArg (fun a:ℕ=>(a:Word w)) equals))

end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
