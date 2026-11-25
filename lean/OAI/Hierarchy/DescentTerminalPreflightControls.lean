import OAI.Hierarchy.DescentTerminalPreflightChronology
import OAI.Hierarchy.DescentTerminalPreflightEarlier
import OAI.Hierarchy.DescentTerminalPlacedAcquiredControls

namespace OAI
/-! # The acquired site directory at the same memory used by the two physical port scatters -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack
open DescentTerminalSpanBook DescentTerminalSiteShelves DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact DescentTerminalRowArena
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 600000
variable (x : Spec) (begin_ rom q piece K codes front : ℕ) (peer : Bank)
    (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank) (total modulo homes : Bank) (boundary : ℕ)
    (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format) (other : Input) (T : RouteSources.Tables)
local notation "W" => x.binSize
local notation "B" => x.pageBits
local notation "grain" => W*piece
local notation "I_" => x.reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other T x.vertices B
local notation "R_" => x.channels begin_
local notation "start" => x.maskBase begin_
local notation "C_" => meter V R_ start
local notation "base_" => afterMeter V cfg R_ start
local notation "A_" => rowArena cfg I_ base_
local notation "X_" => x.controls begin_
local notation "J_" => x.chipInput begin_ rom q grain peer old total modulo homes boundary cfg other
local notation "portTokenBits" => Book.tokenBits (x.vertices*x.arguments)
local notation "M" => x.vertices*x.arguments
variable {w t hN nN aN wid : ℕ} (hq : 0<q) (wp : 0<x.binSize)
    (sites : Fin cfg.sites→Site) (f : ∀i,DescentTerminalLocalPortBook.Room (sites i) 4 x.vertices (x.vertices*x.arguments) x.arguments)
    (labels : ∀i,(sites i).Name→Word (Book.tokenBits (x.vertices*x.arguments))) (refs : ∀i,(sites i).Arg→Word (Book.tokenBits (x.vertices*x.arguments)))
    (perSite : ∀i,(sites i).rows q≤x.binSize)
    (data : Fin cfg.sites→Home (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) («V»:=x.vertices))
variable (head : ℕ) (short : x.vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤x.pageBits)
local notation "literal" => ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses grain x.vertices W B
  cfg.terminal.pool hq (T.columns A_ (J_).sources) (T.value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "loaded" => input (v:=x.vertices) («B»:=B) V cfg I_ R_ start head short literal
local notation "values" => portTable (G:=4) («V»:=x.vertices) («M»:=M) («A»:=x.arguments) («a»:=portTokenBits) q
local notation "expr" => Book.expression (x.parts begin_)
local notation "out_" => x.afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "afterCode" => x.afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "afterTime" => x.afterSiteTime begin_ q grain peer old total modulo homes boundary

attribute [local irreducible] Procedure.Exec CheapCode

include wp perSite short

/-- The site-control source precedes both width scans. All eight selected
directory banks remain readable after both scans and the paid draft. -/
theorem reached_controls_after (m : Memory w) (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors old peer total modulo homes boundary)
    (romTop : rom+DescentTerminalDenseHeaderBoot.extent q grain≤x.literalBase begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w) (positive : 0<w)
    (siteCount : cfg.sites=x.scalar.shops) (rowCount : cfg.terminal.rows=x.paidRows)
    (paidRows : purchased W (counts (q:=q) sites)≤cfg.terminal.rows)
    (poolRows : cfg.terminal.pool≤cfg.terminal.rows)
    (book : Book.Issued (x.parts begin_) (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countWords : ∀i : Fin (Book.Bytes 4 x.vertices M x.arguments portTokenBits),total.read m (i.val:Word w)=countTable q i)
    (boundaryWords : ∀i : Fin (cfg.terminal.rows+1),m (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows).get i)
    (population : ∀i,(data i).1.val=(sites i).nodes) (later : Memory w)
    (partReads : ∀j u,(((I_).parts j).source.read later u=((I_).parts j).source.read (out_ ((X_).after values expr m)) u) ∧
      (((I_).parts j).weights.read later u=((I_).parts j).weights.read (out_ ((X_).after values expr m)) u))
    (directoryReads : ∀j u,((I_).directory j).read later u=((I_).directory j).read (out_ ((X_).after values expr m)) u)
    (countReads : ∀u,total.read later u=total.read (out_ ((X_).after values expr m)) u)
    (boundaryReads : ∀i : Fin (cfg.terminal.rows+1),later (boundary+i.val)=(out_ ((X_).after values expr m)) (boundary+i.val)) :
    let atSite := (X_).after values expr m
    let atPorts := out_ atSite
    (((X_).program w values expr).seq (afterCode w)).Exec m atPorts ((X_).time expr+afterTime) ∧
      CheapCode (((X_).program w values expr).seq (afterCode w)) ∧
      Controls (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) («V»:=x.vertices) («W»:=W) («B»:=B) (n:=cfg.terminal.pool) (plan_).directory
        (Suffix.sockets cfg plan_ ((A_).mount (loaded later))) sites perSite data ∧
      ∀a<x.weights begin_,atPorts a=m a := by
  intro atSite atPorts
  have early := x.earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T x.vertices B paid actors boot romTop full space
  obtain ⟨s0,s1,s2,s3,s4⟩:=stages cfg I_ base_
  have meterStart : start ≤ (C_).base := Nat.le_add_right ..
  have above : start ≤ base_ := meterStart.trans
    ((((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))
  have word := above.trans_lt (((A_).start_le 22).trans_lt
    (s0.trans_lt (s1.trans_lt (s2.trans_lt (s3.trans_lt (s4.trans_lt space))))))
  obtain ⟨l0,l1,l2,l3,l4,l5,l6,l7,l8⟩:=x.layers begin_
  have books := l0.trans (l1.trans (l2.trans l3))
  have high : x.bookEnd begin_<2^w := (l4.trans (l5.trans (l6.trans (l7.trans l8)))).trans_lt word
  have fit (b : Bank) (end_ : b.base+b.size≤x.bookEnd begin_) : b.Fits w (x.bookEnd begin_) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt high),end_⟩
  have low : (rowArena cfg I_ (x.bookEnd begin_)).Lower w :=
    ⟨fun j=>fit _ (x.book_banks begin_ j).1,fun j=>fit _ ((x.book_banks begin_ j).2.trans l3),
     fit _ (boot.total.trans books),fit _ (boot.modulo.trans books),fit _ (boot.homes.trans books)⟩
  let ctrl := DescentTerminalControlProgram.layout (x.bookEnd begin_) cfg.sites 4 x.vertices
    M x.arguments portTokenBits x.vertices W B
  have same : ctrl=X_ := by unfold ctrl controls; rw [siteCount]
  have bound : boundary+(cfg.terminal.rows+1)≤x.bookEnd begin_ := by
    rw [rowCount];exact boot.boundary.trans books
  have stay := x.after_site_run begin_ q grain peer old total modulo homes boundary atSite paid actors boot word positive
  have retain (b : Bank) (below : b.base+b.size≤(X_).finish) (u : Word w) :
      b.read atPorts u=b.read atSite u :=
    stay.2.2 _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le below)
  have placedCore := placed_acquired_banks (w := w) («W» := W) (q := q) (G := 4) («V» := x.vertices)
    («M» := M) (K := x.arguments) («a» := portTokenBits) («B» := B) (t := t) (hN:=hN) (nN:=nN)
    (aN:=aN) (wid:=wid) (verts:=x.vertices) (count:=x.vertices)
    V cfg I_ R_ start head short literal (x.bookEnd begin_) m low early space
  have placedPaid := placedCore sites f labels refs wp perSite paidRows bound book countWords boundaryWords poolRows
  have placedDirectory := placedPaid
    (show (I_).directory=DescentTerminalControlProgram.earlyBanks ctrl (I_).parts by rw [same];rfl)
    (show ctrl.finish≤ start by rw [same]; exact l5.trans (l6.trans (l7.trans l8))) data population later
  have done_ := placedDirectory
    (by
      change ∀j u,_=(((I_).parts j).source.read (ctrl.after values expr m) u) ∧
        _=(((I_).parts j).weights.read (ctrl.after values expr m) u)
      rw [same]
      exact fun j u=>⟨((partReads j u).1).trans (retain _ ((x.book_banks begin_ j).1.trans l4) u),
        ((partReads j u).2).trans (retain _ ((x.book_banks begin_ j).2.trans (l3.trans l4)) u)⟩)
    (by
      change ∀j u,_=((I_).directory j).read (ctrl.after values expr m) u
      rw [same]
      exact fun j u=>(directoryReads j u).trans (retain _ (DescentTerminalControlProgram.early_before
        X_ (x.parts begin_) (x.book_banks begin_ 1).1 j) u))
    (by
      change ∀u,_=total.read (ctrl.after values expr m) u
      rw [same]
      exact fun u=>(countReads u).trans (retain _ (boot.total.trans (books.trans l4)) u))
    (by
      change ∀i:Fin (cfg.terminal.rows+1),_=ctrl.after values expr m (boundary+i.val)
      rw [same]
      exact fun i=>(boundaryReads i).trans (stay.2.2 _ ((Nat.add_lt_add_left i.isLt _).trans_le (bound.trans l4))))
  have originalControl := done_.2.2.1
  change (ctrl.program w values expr).Exec m (ctrl.after values expr m) (ctrl.time expr) ∧
    CheapCode (ctrl.program w values expr) ∧ _ at done_
  rw [same] at done_
  obtain ⟨dRun,dCheap,dControl,dKept⟩ := done_
  obtain ⟨sRun,sCheap,sKept⟩ := stay
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @Procedure.Exec.then w ((X_).program w values expr) (afterCode w) m atSite atPorts
      ((X_).time expr) afterTime (@dRun) (@sRun)
  · exact @cheap_seq w ((X_).program w values expr) (afterCode w) (@dCheap) (@sCheap)
  · exact originalControl
  · intro i hi
    have lowBook : i<x.bookEnd begin_ := hi.trans_le (l2.trans l3)
    have atEq : ctrl.after values expr m = atSite :=
      congrArg (fun y : DescentTerminalControlProgram.Plan => y.after values expr m) same
    exact (sKept i (lowBook.trans_le l4)).trans
      ((congrFun atEq.symm i).trans (dKept i (.inl lowBook)))

theorem reached_controls (m : Memory w) (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors old peer total modulo homes boundary)
    (romTop : rom+DescentTerminalDenseHeaderBoot.extent q grain≤x.literalBase begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space : last V cfg I_ R_ start<2^w) (positive : 0<w)
    (siteCount : cfg.sites=x.scalar.shops) (rowCount : cfg.terminal.rows=x.paidRows)
    (paidRows : purchased W (counts (q:=q) sites)≤cfg.terminal.rows)
    (poolRows : cfg.terminal.pool≤cfg.terminal.rows)
    (book : Book.Issued (x.parts begin_) (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countWords : ∀i : Fin (Book.Bytes 4 x.vertices M x.arguments portTokenBits),total.read m (i.val:Word w)=countTable q i)
    (boundaryWords : ∀i : Fin (cfg.terminal.rows+1),m (boundary+i.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows).get i)
    (population : ∀i,(data i).1.val=(sites i).nodes) :
    let atSite := (X_).after values expr m
    let atPorts := out_ atSite
    (((X_).program w values expr).seq (afterCode w)).Exec m atPorts ((X_).time expr+afterTime) ∧
      CheapCode (((X_).program w values expr).seq (afterCode w)) ∧
      Controls (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) («V»:=x.vertices) («W»:=W) («B»:=B) (n:=cfg.terminal.pool) (plan_).directory
        (Suffix.sockets cfg plan_ ((A_).mount (loaded atPorts))) sites perSite data ∧
      ∀a<x.weights begin_,atPorts a=m a := by
  exact x.reached_controls_after begin_ rom q piece K codes front peer old total modulo homes boundary
    cfg V other T hq wp sites f labels refs perSite data head short m paid actors boot romTop full space
    positive siteCount rowCount paidRows poolRows book countWords boundaryWords population
    (out_ ((X_).after values expr m)) (fun _ _=>⟨rfl,rfl⟩) (fun _ _=>rfl) (fun _=>rfl) (fun _=>rfl)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
