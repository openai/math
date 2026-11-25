import OAI.Hierarchy.ProtocolRAMTurnAfterReplay
import OAI.Hierarchy.TaggedWireTurnLive

namespace OAI
/-! # The old and settled native role banks and the real bit-offset ranks coexist -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnReplayed
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.RouteSettlement ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native CoreBoard HistoryRoles RoleProgram
open scoped Classical Fin.CommRing
variable {w K edges r h W k attempts : ℕ} {I C : Type} [Fintype I] [Fintype C]

theorem role_frame (b : Board) (g : Inventory) (m : Memory w) (a : ℕ) (low : a<b.base) :
    b.extendedState g m a=m a := by
  have fresh : a<b.newBase := low.trans_le (Nat.le_add_right ..)
  have last : a<b.endAt := fresh.trans_le (Nat.le_add_right ..)
  calc
    _ = b.final m a := columns_frame (List.ofFn (b.rawFields g)) (b.final m) (.inl last)
    _ = state b.base b.old b.chart b.before false m a :=
      columns_frame (List.ofFn (field b.chart b.finish true)) _ (.inl fresh)
    _ = m a := columns_frame (List.ofFn (field b.chart b.before false)) _ (.inl low)

theorem reserve_after_bank (L : PrefixWidths.Layout edges) (last axes : ℕ) {count : ℕ}
    (fit : count≤2^axes) : (L.bank last).base+(L.bank last).size<(L.reserveLayout axes last fit).archive := by
  change L.archive+last*(2^L.bits+1)+2^L.bits<L.archive+(last+1)*(2^L.bits+1)
  rw [Nat.succ_mul]
  omega

omit [Fintype I] [Fintype C] in
/-- The role program reads the actual replayed paid page. Its result is carried through
the next native rank computation, retaining the lower archive and all eleven role columns. -/
private theorem final_rank (S : PurchaseSampler) (b : Board) (g : Inventory)
    (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (settlement : Banks) (archive m : Memory w) {paidSource : Memory w} (ci : I→ℕ) (cj : C→ℕ)
    (existsDir : Directory settlement archive enum ci cj)
    (low : ∀c∈[settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],c.base+c.size≤L.archive)
    (keep : ∀x<L.archive,m x=archive x)
    (paid : ∀i : Fin edges,(m ((L.bank (events calendar).length).base+i.val)).val=
      PaidWidths.total ((events calendar).flatMap compile) paidSource i)
    (before : (L.bank (events calendar).length).base+edges≤b.base)
    (after : b.endAt+3*b.old≤lo) (oldRoom : b.old≤2^w) (newRoom : b.edges≤2^w)
    (inputs : ∀c∈[L.bank (events calendar).length,settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],
      c.Fits w lo) (room : endAt lo (edges+r) edges<2^w) (wide : 2<2^w)
    (budget : ∀j,actual settlement.used archive (cj j)≤actual settlement.reserved archive (cj j))
    (old : Fin b.old→ℕ) (finalWidth : Fin b.edges→ℕ)
    (left : ∀i,0<old i→Bool→Public S h W k attempts) (right : ∀i,0<finalWidth i→Bool→Public S h W k attempts)
    (reads : b.LiveReads S old finalWidth left right (b.extendedState g m))
    (p : Procedure w) (raw : Memory w) (ticks : ℕ) (ran : p.Exec raw (b.extendedState g m) ticks) (archiveRows : Bool := false) :
    let n:=edges+r
    let widths:=B.nativeWidth enum (fun i=>PaidWidths.total ((events calendar).flatMap compile) paidSource i)
      (fun i=>actual settlement.stock archive (ci i)) (fun j=>actual settlement.reserved archive (cj j))
      (fun j=>actual settlement.used archive (cj j))
    ∃ out, (p.seq (procedure w lo edges r settlement (L.bank (events calendar).length))).Exec raw out
      (ticks+(66+539*n+6*edges)) ∧ b.LiveReads S old finalWidth left right out ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word w)) ∧
      (∀x <b.base,out x=m x) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word w)) ∧
      let readWidths:=∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word w)
      if archiveRows then (∀a<lo,out a=b.extendedState g m a) ∧ readWidths else readWidths := by
  intro n widths
  let last:=(events calendar).length
  have oldLow : L.archive≤b.base := (L.archive_le last).trans ((Nat.le_add_right ..).trans before)
  have keep' (x : ℕ) (hx : x<L.archive) : b.extendedState g m x=archive x :=
    (role_frame b g m x (hx.trans_le oldLow)).trans (keep x hx)
  have paid' (i : Fin edges) : (b.extendedState g m ((L.bank last).base+i.val)).val=
      PaidWidths.total ((events calendar).flatMap compile) paidSource i := by
    rw [role_frame b g m _ ((Nat.add_lt_add_left i.isLt _).trans_le before)]
    exact paid i
  obtain ⟨out,exec,starts,frame,keys,weights⟩:=after_last B enum calendar compile L lo settlement archive
    (b.extendedState g m) ci cj existsDir low keep' paid' inputs room wide budget
    p raw ticks ran
  have below : b.base≤lo := (Nat.le_add_right .. : b.base≤b.newBase).trans
    ((Nat.le_add_right .. : b.newBase≤b.endAt).trans ((Nat.le_add_right ..).trans after))
  exact ⟨out,exec,Board.LiveReads.frame (S := S) (b := b) reads lo after oldRoom newRoom frame,starts,
    fun x hx=>(frame x (hx.trans_le below)).trans (role_frame b g m x hx),keys,by cases archiveRows <;> first | exact weights | exact ⟨frame,weights⟩⟩

omit [Fintype I] [Fintype C] in
theorem rank_after_roles_last (S : PurchaseSampler) (b : Board) (g : Inventory)
    (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (settlement : Banks) (archive m : Memory w) {paidSource : Memory w} (ci : I→ℕ) (cj : C→ℕ)
    (existsDir : Directory settlement archive enum ci cj)
    (low : ∀c∈[settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],c.base+c.size≤L.archive)
    (keep : ∀x<L.archive,m x=archive x)
    (paid : ∀i : Fin edges,(m ((L.bank (events calendar).length).base+i.val)).val=
      PaidWidths.total ((events calendar).flatMap compile) paidSource i)
    (before : (L.bank (events calendar).length).base+edges≤b.base)
    (after : b.endAt+3*b.old≤lo) (oldRoom : b.old≤2^w) (newRoom : b.edges≤2^w)
    (inputs : ∀c∈[L.bank (events calendar).length,settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],
      c.Fits w lo) (room : endAt lo (edges+r) edges<2^w) (wide : 2<2^w)
    (budget : ∀j,actual settlement.used archive (cj j)≤actual settlement.reserved archive (cj j))
    (old : Fin b.old→ℕ) (finalWidth : Fin b.edges→ℕ)
    (left : ∀i,0<old i→Bool→Public S h W k attempts) (right : ∀i,0<finalWidth i→Bool→Public S h W k attempts)
    (resolved : (b.extended g w).Exec m (b.extendedState g m) (b.extendedTime g) ∧
      b.LiveReads S old finalWidth left right (b.extendedState g m)) (archiveRows : Bool := false)
    :
    let n:=edges+r
    let widths:=B.nativeWidth enum (fun i=>PaidWidths.total ((events calendar).flatMap compile) paidSource i)
      (fun i=>actual settlement.stock archive (ci i)) (fun j=>actual settlement.reserved archive (cj j))
      (fun j=>actual settlement.used archive (cj j))
    ∃ out, ((b.extended g w).seq (procedure w lo edges r settlement (L.bank (events calendar).length))).Exec m out
      (b.extendedTime g+(66+539*n+6*edges)) ∧ b.LiveReads S old finalWidth left right out ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word w)) ∧
      (∀x <b.base,out x=m x) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word w)) ∧
      let readWidths:=∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word w)
      if archiveRows then (∀a<lo,out a=b.extendedState g m a) ∧ readWidths else readWidths :=
  final_rank S b g B enum calendar compile L lo settlement archive m ci cj existsDir low keep paid before after oldRoom newRoom inputs room wide budget old finalWidth left right resolved.2 (b.extended g w) m (b.extendedTime g) resolved.1 archiveRows

omit [Fintype I] [Fintype C] in
theorem rank_after_roles (S : PurchaseSampler) (b : Board) (g : Inventory)
    (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (settlement : Banks) (archive m : Memory w) {paidSource : Memory w} (ci : I→ℕ) (cj : C→ℕ)
    (existsDir : Directory settlement archive enum ci cj)
    (low : ∀c∈[settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],c.base+c.size≤L.archive)
    (keep : ∀x<L.archive,m x=archive x)
    (paid : ∀j≤(events calendar).length,∀i : Fin edges, (m ((L.bank j).base+i.val)).val=
      PaidWidths.total (PrefixWidths.prefixRows (events calendar) compile j) paidSource i)
    (before : (L.bank (events calendar).length).base+edges≤b.base)
    (after : b.endAt+3*b.old≤lo) (oldRoom : b.old≤2^w) (newRoom : b.edges≤2^w)
    (inputs : ∀c∈[L.bank (events calendar).length,settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],
      c.Fits w lo) (room : endAt lo (edges+r) edges<2^w) (wide : 2<2^w)
    (budget : ∀j,actual settlement.used archive (cj j)≤actual settlement.reserved archive (cj j))
    (old : Fin b.old→ℕ) (finalWidth : Fin b.edges→ℕ)
    (left : ∀i,0<old i→Bool→Public S h W k attempts) (right : ∀i,0<finalWidth i→Bool→Public S h W k attempts)
    (resolved : (b.extended g w).Exec m (b.extendedState g m) (b.extendedTime g) ∧
      b.LiveReads S old finalWidth left right (b.extendedState g m))
    :
    let n:=edges+r
    let widths:=B.nativeWidth enum (fun i=>PaidWidths.total ((events calendar).flatMap compile) paidSource i)
      (fun i=>actual settlement.stock archive (ci i)) (fun j=>actual settlement.reserved archive (cj j))
      (fun j=>actual settlement.used archive (cj j))
    ∃ out, ((b.extended g w).seq (procedure w lo edges r settlement (L.bank (events calendar).length))).Exec m out
      (b.extendedTime g+(66+539*n+6*edges)) ∧ b.LiveReads S old finalWidth left right out ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word w)) ∧
      (∀x <b.base,out x=m x) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word w)) ∧
      ∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word w) := by
  apply final_rank S b g B enum calendar compile L lo settlement archive m ci cj existsDir low keep _ before after oldRoom newRoom inputs room wide budget old finalWidth left right resolved.2 (b.extended g w) m (b.extendedTime g) resolved.1
  intro i
  simpa only [PrefixWidths.prefixRows,List.take_length] using paid (events calendar).length le_rfl i

omit [Fintype I] [Fintype C] in
theorem roles_then_rank (S : PurchaseSampler) (b : Board) (g : Inventory)
    (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (settlement : Banks) (archive m : Memory w) {paidSource : Memory w} (ci : I→ℕ) (cj : C→ℕ)
    (existsDir : Directory settlement archive enum ci cj)
    (low : ∀c∈[settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],c.base+c.size≤L.archive)
    (keep : ∀x<L.archive,m x=archive x)
    (paid : ∀j≤(events calendar).length,∀i : Fin edges, (m ((L.bank j).base+i.val)).val=
      PaidWidths.total (PrefixWidths.prefixRows (events calendar) compile j) paidSource i)
    (before : (L.bank (events calendar).length).base+edges≤b.base)
    (after : b.endAt+3*b.old≤lo) (oldRoom : b.old≤2^w) (newRoom : b.edges≤2^w)
    (inputs : ∀c∈[L.bank (events calendar).length,settlement.index,settlement.kind,settlement.stock,settlement.reserved,settlement.used],
      c.Fits w lo) (room : endAt lo (edges+r) edges<2^w) (wide : 2<2^w)
    (budget : ∀j,actual settlement.used archive (cj j)≤actual settlement.reserved archive (cj j))
    (old : Fin b.old→ℕ) (finalWidth : Fin b.edges→ℕ)
    (left : ∀i,0<old i→Bool→Public S h W k attempts) (right : ∀i,0<finalWidth i→Bool→Public S h W k attempts)
    (resolved : (b.extended g w).Exec m (b.extendedState g m) (b.extendedTime g) ∧
      b.LiveReads S old finalWidth left right (b.extendedState g m))
    (p : Procedure w) (raw : Memory w) (ticks : ℕ) (ran : p.Exec raw m ticks) :
    let n:=edges+r
    let widths:=B.nativeWidth enum (fun i=>PaidWidths.total ((events calendar).flatMap compile) paidSource i)
      (fun i=>actual settlement.stock archive (ci i)) (fun j=>actual settlement.reserved archive (cj j))
      (fun j=>actual settlement.used archive (cj j))
    ∃ out, ((p.seq (b.extended g w)).seq (procedure w lo edges r settlement (L.bank (events calendar).length))).Exec raw out
      ((ticks+b.extendedTime g)+(66+539*n+6*edges)) ∧ b.LiveReads S old finalWidth left right out ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word w)) ∧
      (∀x <b.base,out x=m x) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word w)) ∧
      ∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word w) := by
  apply final_rank S b g B enum calendar compile L lo settlement archive m ci cj existsDir low keep _ before after oldRoom newRoom inputs room wide budget old finalWidth left right resolved.2 (p.seq (b.extended g w)) raw (ticks+b.extendedTime g) (Procedure.Exec.then ran resolved.1)
  intro i
  simpa only [PrefixWidths.prefixRows,List.take_length] using paid (events calendar).length le_rfl i

end Hierarchy.ProtocolRAMTurnReplayed
end

end OAI
