import OAI.Hierarchy.DescentTerminalPaidHeaderRAM
import OAI.Hierarchy.DescentTerminalSiteCursorPlan
import OAI.Hierarchy.DescentTerminalRowArenaPrime
import OAI.Hierarchy.DescentTerminalRowPlanNames
import OAI.Hierarchy.DescentTerminalRowFrames

namespace OAI
/-! # A fixed row-plan checkpoint to issue header incidences before the final scalar pass -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalRowArena DescentTerminalPaidHeaderEvents DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalBinPack
open scoped Classical Fin.CommRing
noncomputable section
variable (A:Arena) (L:DescentTerminalHeaderSockets.Layout) (D:ℕ)

def inputs : Inputs := ⟨L,A.row.locate.active,A.row.locate.owner,A.row.locate.localRow⟩
def newBank (k:ℕ) : Bank := ⟨A.finish+k*(2^Nat.clog 2 A.rows),Nat.clog 2 A.rows⟩
def output : Output := ⟨newBank A 0,newBank A 1,newBank A 2⟩
def stop := A.finish+3*(2^Nat.clog 2 A.rows)
local notation "I" => inputs A L
local notation "O" => output A
def rowed {w:ℕ} (m:Memory w) := DescentTerminalRowPlan.result A.row A.sites A.rows (A.mount m)
def data {w:ℕ} (m:Memory w) := after I O A.sites D A.rows (rowed A m)
def machine (w:ℕ) := ((A.prime w).seq (DescentTerminalRowPlan.program (w:=w) A.row A.sites A.rows)).seq
  (DescentTerminalPaidHeaderEvents.program I O A.sites D A.rows w)
def clocks := (8+104*A.sites+DescentTerminalRowPlan.time A.row A.sites A.rows)+ticks I A.sites D A.rows
structure Room (w:ℕ) : Prop where
  lower : A.Lower w
  area : stop A<2^w
  fields : ∀c:Column,(expr I A.sites D c).Fits w A.finish

variable {w:ℕ} (m:Memory w) (ok:Room A L D w)
include ok in
theorem arenaFit : A.finish<2^w := by have:=ok.area;unfold stop at this;omega
include ok in
theorem eventRoom : DescentTerminalPaidHeaderEvents.Room I O A.sites D A.rows w := by
  have h:A.rows≤2^Nat.clog 2 A.rows:=Nat.le_pow_clog (by decide) _
  have top:=ok.area
  unfold stop at top
  constructor
  · intro c;simpa only [output,newBank,Nat.zero_mul,Nat.add_zero] using ok.fields c
  · change A.finish+0*(2^Nat.clog 2 A.rows)+A.rows≤A.finish+1*(2^Nat.clog 2 A.rows);omega
  · change A.finish+1*(2^Nat.clog 2 A.rows)+A.rows≤A.finish+2*(2^Nat.clog 2 A.rows);omega
  · change A.finish+2*(2^Nat.clog 2 A.rows)+A.rows<2^w;omega

private theorem three_runs {w : ℕ} (P Q R : Procedure w) (m m₁ m₂ m₃ : Memory w)
    (a b c : ℕ) (first : P.Exec m m₁ a ∧ CheapCode P)
    (second : Q.Exec m₁ m₂ b ∧ CheapCode Q) (third : R.Exec m₂ m₃ c ∧ CheapCode R) :
    ((P.seq Q).seq R).Exec m m₃ ((a+b)+c) ∧ CheapCode ((P.seq Q).seq R) :=
  @exec_cheap_seq w (a+b) c (P.seq Q) R m m₂ m₃
    (@exec_cheap_seq w a b P Q m m₁ m₂ first second) third

include ok in
theorem any (pos:0<w) :
    (machine A L D w).Exec m (data A L D m) (clocks A L D) ∧ CheapCode (machine A L D w) := by
  have capacity:=arenaFit A L D ok
  unfold machine data clocks
  exact three_runs (A.prime w) (DescentTerminalRowPlan.program (w:=w) A.row A.sites A.rows)
    (DescentTerminalPaidHeaderEvents.program I O A.sites D A.rows w)
    m (A.mount m) (rowed A m) (after I O A.sites D A.rows (rowed A m))
    (8+104*A.sites) (DescentTerminalRowPlan.time A.row A.sites A.rows) (ticks I A.sites D A.rows)
    (A.prime_run m capacity)
    (DescentTerminalRowPlan.run A.row A.sites A.rows (A.mount m)
      (A.row_room ok.lower capacity) pos (A.mounted_fixed capacity m))
    (executed I O A.sites D A.rows (rowed A m) (eventRoom A L D ok))

def effort := (expr I A.sites D .active).work+(expr I A.sites D .mode).work+(expr I A.sites D .source).work
open DescentTerminalHeaderSockets in
/-- The actual terminal branch has three signed aperture slots. The syntactic work is
independent of every bank base, output length, and numerical cardinal of the host. -/
theorem effort_three : effort A L 3=70127 := by
  let v : Expr := .lookup (I).owner .row
  have offsets : List.finRange 3 = [(0:Fin 3),1,2] := by decide
  have reverseCost (j : ℕ) :
      (reverse (I).sockets v (targetAt (I).sockets v 3 j) 3 (List.finRange 3)).work = 658 := by
    simp only [offsets,reverse,successor,targetAt,DescentTerminalHeaderSockets.offset,times,Expr.work,v]
  have cableKey (j : ℕ) : (canonical (I).sockets v A.sites 3 j).work = 762 := by
    simp only [canonical,Expr.work,reverseCost]
    simp only [successor,targetAt,DescentTerminalHeaderSockets.offset,times,Expr.work,v]
  have publicHead : (head (I).sockets A.sites 3 v (0:Fin 4)).work = 28 := by rfl
  have publicAmount : (amount (I).sockets A.sites 3 v (0:Fin 4)).work = 57 := by rfl
  have cableHead (t : Fin 3) : (head (I).sockets A.sites 3 v t.succ).work = 1534 := by
    simp only [head,Fin.cases_succ,starts,Expr.work,cableKey]
  have cableAmount (t : Fin 3) : (amount (I).sockets A.sites 3 v t.succ).work = 3069 := by
    simp only [amount,Fin.cases_succ,ends,starts,Expr.work,cableKey]
  dsimp only [v] at publicHead publicAmount cableHead cableAmount
  have slots : List.finRange 4 = [(0:Fin 4),(0:Fin 3).succ,(1:Fin 3).succ,(2:Fin 3).succ] := by decide
  simp only [effort,expr,slots,choose,Expr.work,publicHead,publicAmount,cableHead,cableAmount]

theorem price (w:ℕ) :
    DescentStaticWordColumn.names (machine A L D w)=1400+4*effort A L D ∧
      clocks A L D≤8+104*A.sites+1024*(A.sites+A.rows+1)+12+A.rows*(2*effort A L D+12) := by
  have plan:=DescentTerminalRowPlan.tariff A.row A.sites A.rows
  have prime:=A.prime_text w
  change DescentStaticWordColumn.names (A.prime w)=110 at prime
  constructor
  · simp only [machine,DescentStaticWordColumn.names_seq,prime,DescentTerminalRowPlan.program_names,
      DescentTerminalPaidHeaderEvents.tariff,effort];omega
  · unfold clocks ticks effort
    nlinarith

include ok in
theorem row_low (j:ℕ) (early:j<A.start) : rowed A m j=m j := by
  have h (k:ℕ) : j<A.atBand k:=by change j<A.start+k*A.stride;omega
  exact (DescentTerminalRowPlan.before_publishing A.row _ (A.row_room ok.lower (arenaFit A L D ok))
    ⟨h 9,h 7,h 6,h 5,h 4,h 3⟩ (h 2)).trans (A.mount_before _ early)

include ok in
theorem lowFrame (j:ℕ) (early:j<A.start) : data A L D m j=m j := by
  have below:j<(output A).active.base:=by change j<A.start+22*A.stride+0*(2^Nat.clog 2 A.rows);omega
  exact (before I O A.sites D A.rows (rowed A m) (eventRoom A L D ok) j below).trans (row_low A L D m ok j early)

variable {W q G V M K a:ℕ} (sites:Fin A.sites→Site) (room:∀v,DescentTerminalLocalPortBook.Room (sites v) G V M K)
    (labels:∀v,(sites v).Name→Word a) (refs:∀v,(sites v).Arg→Word a)
    (wp:0<W) (fit:∀v,(sites v).rows q≤W) (paid:purchased W (counts (q:=q) sites)≤A.rows)
    (counter:A.rows+W<2^w) (bounds:A.boundaries+(A.rows+1)≤A.start)
    (book:Book.Issued A.parts (fun v=>issue (sites v) (room v) (labels v) (refs v)) m)
    (countRom:∀j:Fin (Book.Bytes G V M K a),A.countTable.read m (j.val:Word w)=countTable q j)
    (boundRom:∀j:Fin (A.rows+1),m (A.boundaries+j.val)=(DescentTerminalBinPackCheap.boundaries w W A.rows)[j.val])
include ok wp paid counter bounds book countRom boundRom in
theorem cursors (i:Fin A.rows) :
    A.row.locate.Facts sites i fit (rowed A m) :=
  A.issued_owner m ok.lower (arenaFit A L D ok) sites room labels refs wp fit paid counter bounds book countRom boundRom i

end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
