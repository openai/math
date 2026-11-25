import OAI.Hierarchy.DescentTerminalPreflightControls
import OAI.Hierarchy.DescentTerminalPreflightReelFrame

namespace OAI
/-! # The original acquired site directory after the final exterior reel -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack
open DescentTerminalSpanBook DescentTerminalSiteShelves DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact DescentTerminalRowArena
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 550000
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

include wp perSite short

/-- The genuine relocation and fold may update their own scratch words. The
booked controls are queried on their protected banks at the new terminal date. -/
theorem reel_controls (m : Memory w) (paid actors : Fin x.scalar.blocks→Bank)
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
    (population : ∀i,(data i).1.val=(sites i).nodes)
    (post : Memory w) (fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→post a=out_ ((X_).after values expr m) a)
    (late : dst<x.cohortEnd begin_) (ceiling : start≤fence)
    (countSide : total.base+total.size≤firstFree ∨ dst<total.base)
    (boundSide : boundary+(x.paidRows+1)≤firstFree ∨ dst<boundary) :
    let atSite := (X_).after values expr m
    let atPorts := out_ atSite
    (((X_).program w values expr).seq (afterCode w)).Exec m atPorts ((X_).time expr+afterTime) ∧
      CheapCode (((X_).program w values expr).seq (afterCode w)) ∧
      Controls (q:=q) (t:=t) (H:=hN) (N:=nN) («A»:=aN) (w:=wid) («V»:=x.vertices) («W»:=W) («B»:=B) (n:=cfg.terminal.pool) (plan_).directory
        (Suffix.sockets cfg plan_ ((A_).mount (loaded post))) sites perSite data ∧
      ∀a<x.weights begin_,atPorts a=m a := by
  have frames := x.reel_control_ranges begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T x.vertices B (out_ ((X_).after values expr m)) post fence firstFree dst saved late ceiling
    paid actors boot rowCount countSide boundSide
  exact x.reached_controls_after begin_ rom q piece K codes front peer old total modulo homes boundary
    cfg V other T hq wp sites f labels refs perSite data head short m paid actors boot romTop full space
    positive siteCount rowCount paidRows poolRows book countWords boundaryWords population post
    frames.1 frames.2.1 frames.2.2.1 frames.2.2.2

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
