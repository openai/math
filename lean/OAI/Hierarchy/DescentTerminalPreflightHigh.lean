import OAI.Hierarchy.DescentTerminalPreflightChronology
import OAI.Hierarchy.DescentTerminalRowArenaHigh
import OAI.Hierarchy.DescentTerminalWeightShelf

namespace OAI
/-! # Upper memory frames for the six book lookups and the native header preflight -/
namespace Hierarchy
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderDraft DescentTerminalHeaderSockets DescentTerminalRowArena
open DescentTerminalPointerDigits DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

namespace DescentTerminalLocalPortBook.Print.Layout

theorem memory_high {L G V A w : ℕ} (P : Layout L) (decode : (Fin L→Cell P.bits)→Directory G V A)
    (M : ℕ) (m : Memory w) (fits : ∀j,(P.source j).Fits w P.start)
    (digit : 2^P.bits<2^w) (room : P.stop<2^w) (n : ℕ) (hn : n≤6) (a : ℕ) (late : P.origin n≤a) :
    P.memory decode M m n hn a=m a := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    let i : Fin 6:=⟨n,by omega⟩
    let prior:=P.memory decode M m n (by omega)
    have chain {i j : ℕ} (h : i≤j) : P.origin i≤P.origin j :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
    have keep:=ih (by omega) (by exact (chain (Nat.le_succ n)).trans late)
    have room' : (P.bank n).base+P.homes≤P.origin (n+1) :=
      (Nat.add_le_add_left (Nat.le_pow_clog (by decide) P.homes) _).trans (P.end_bank n).le
    have top : P.origin (n+1)<2^w := (chain hn).trans_lt room
    have low : P.start≤P.origin n:=Nat.le_add_right ..
    have run:=Gather.execute (P.origin n) P.homes P.source (P.field decode M i) prior
      (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits j)) digit (room'.trans_lt top)
    exact (run.2.2.2 a (.inr (room'.trans late))).trans keep

end DescentTerminalLocalPortBook.Print.Layout

namespace DescentTerminalLocalPortBook.Book.WeightShelf

theorem memory_high (V A base : ℕ) {w : ℕ} (m : Memory w) {a : ℕ} (late : finish V A base≤a) :
    memory V A base m a=m a :=
  DescentStaticWordColumn.frame base (words V A) _ m a (.inr late)

end DescentTerminalLocalPortBook.Book.WeightShelf

namespace DescentTerminalGrainProfiles.Counter.Rack

theorem final_high {blocks cap groups M w : ℕ} (T : Rack blocks cap groups M) (q p : ℕ) (m : Memory w)
    (fit : T.Fits w) (a : ℕ) (late : T.printer.stop≤a) : T.final q p m a=m a := by
  obtain ⟨lo,mid,first,last⟩:=T.gaps
  have pad : T.population.base+T.population.size=T.printer.origin:=rfl
  have endAt : T.population.base+T.tickets<2^w:=first.trans_lt (last.trans_lt fit.space)
  have count:=issue T.degree T.scale T.lanes T.base T.tickets _ _ T.cables (T.boot m)
    (T.read_room fit) fit.digit endAt
  have fit' : T.population.Fits w T.printer.origin :=
    ⟨Nat.two_pow_pos _,by have := last.trans_lt fit.space;omega,pad.le⟩
  have floor : T.slab≤T.population.base:=Nat.le_add_right ..
  have start : T.base≤a:=by omega
  exact (T.printer.frame_any q p w (T.counters m) fit' fit.space a (.inr late)).trans
    ((count.2.2.2 a (.inr (first.trans (last.trans late)))).trans
      (DescentStaticWordColumn.frame T.sockets.origin (3*(T.sockets.home T.homes T.degree).size)
        _ m a (.inr start)))

end DescentTerminalGrainProfiles.Counter.Rack

namespace DescentTerminalPublicWidthTape.Shape

theorem last_high (S : Shape) (q p : ℕ) {w : ℕ} (m : Memory w)
    (room : S.widthLayout.stop<2^w) (a : ℕ) (late : S.widthLayout.stop≤a) :
    S.lastMem q p m a=m a := by
  have source:=DescentTerminalPublicCountRAM.bank_fits S.base S.maxCohorts S.H (S.scale_space room)
  have prior : S.widthLayout.origin≤a := by
    have p₁ : S.widthLayout.origin≤S.widthLayout.prefix.base:=Nat.le_add_right ..
    change S.widthLayout.prefix.base+S.widthLayout.prefix.size+S.widthLayout.output.size+1+
      S.widthLayout.groups+S.widthLayout.groups≤a at late
    omega
  exact (S.widthLayout.frame_any q p w _ source room a (.inr late)).trans
    (DescentTerminalPublicCountRAM.frame S.base S.maxCohorts S.H S.old S.rate m a (.inr prior))

end DescentTerminalPublicWidthTape.Shape

namespace DescentTerminalHeaderDraft

theorem highFrame (A : Arena) (L : DescentTerminalHeaderSockets.Layout) (D : ℕ) {w : ℕ} (m : Memory w)
    (ok : Room A L D w) (i : ℕ) (late : stop A≤ i) : data A L D m i=m i := by
  have span : A.rows≤2^Nat.clog 2 A.rows:=Nat.le_pow_clog (by decide) _
  change A.finish+3*(2^Nat.clog 2 A.rows)≤ i at late
  have old : A.finish≤ i:=by omega
  have n0 : (output A).active.base+A.rows≤ i := by change A.finish+0*(2^Nat.clog 2 A.rows)+A.rows≤ i;omega
  have n1 : (output A).mode.base+A.rows≤ i := by change A.finish+1*(2^Nat.clog 2 A.rows)+A.rows≤ i;omega
  have n2 : (output A).source.base+A.rows≤ i := by change A.finish+2*(2^Nat.clog 2 A.rows)+A.rows≤ i;omega
  have tail : rowed A m i=A.mount m i:=A.plan_after (A.mount m) (arenaFit A L D ok) old
  have size:=A.stride_min
  have past (k : ℕ) (hk : k<22) : ¬i<A.atBand k+2*A.sites :=
    not_lt.mpr (((Nat.add_le_add_left (by omega : 2*A.sites≤A.stride) _).trans (A.band_after hk)).trans old)
  have root : A.mount m i=m i:=by simp [DescentTerminalRowArena.Arena.mount,fillSegment,past 0 (by decide),past 1 (by decide)]
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr n2)).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr n1)).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr n0)).trans (tail.trans root)))

end DescentTerminalHeaderDraft

namespace DescentTerminalPreflightSpace.Spec

theorem after_site_high (x : Spec) (base q p : ℕ) (peer : Bank) (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ) {w : ℕ} (m : Memory w) (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before base paid actors old peer total modulo homes boundary) (room : x.maskBase base<2^w)
    (a : ℕ) (late : x.maskBase base≤a) : x.afterSiteControls base q p peer old total modulo homes boundary m a=m a := by
  let T:=x.cables base peer old
  let U:=x.publicWidths base
  let A:=x.draft base total modulo homes boundary
  let original:=x.afterWidths base q p peer old m
  obtain ⟨_,_,_,_,_,_,l,r,d⟩:=x.layers base
  have fu:=x.after_public base room
  have narrow : x.draftBase base<2^w:=d.trans_lt room
  have ch:=T.final_high q p m (x.fits_cables base room paid actors old peer total modulo homes boundary boot) a
    (by change x.cableEnd base≤a;omega)
  have pub:=U.last_high q p (T.final q p m) fu.2 a (by change x.literalBase base≤a;omega)
  have draft:=highFrame A (x.eventInputs base peer old) x.degree
    (litMem (x.literalBase base) x.paidRows original) (x.fits_draft base room paid actors old peer total modulo homes boundary boot).1
    a (by change x.maskBase base≤a;exact late)
  have set:=lit_install (x.literalBase base) x.paidRows original narrow
  exact draft.trans ((set.2.2.2 a (.inr (d.trans late))).trans (pub.trans ch))

end DescentTerminalPreflightSpace.Spec

end
end Hierarchy

end OAI
