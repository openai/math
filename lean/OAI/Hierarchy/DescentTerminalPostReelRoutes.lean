import OAI.Hierarchy.DescentTerminalPostReelBooks
import OAI.Hierarchy.DescentTerminalPlacedRouteColumns

namespace OAI
/-! # The charged terminal route columns in the state after the original 17-column reel -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentTerminalBinPack
open DescentTerminalSpanBook DescentTerminalSiteShelves DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact DescentTerminalRowArena
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q piece K codes front : ℕ) (peer : Bank)
    (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank) (total modulo homes : Bank) (boundary : ℕ)
    (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format) (other : Input)
local notation "W" => x.binSize
local notation "B" => x.pageBits
local notation "T" => (RouteSources.Tables.mk 4 x.vertices (x.vertices*x.arguments) x.arguments
  (Book.tokenBits (x.vertices*x.arguments)) W q K)
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
local notation "a" => Book.tokenBits (x.vertices*x.arguments)
local notation "M" => x.vertices*x.arguments
variable {w:ℕ} (hq:0<q)
variable (head : ℕ) (short : x.vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ x.pageBits)
local notation "literal" => ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses grain x.vertices W B
  cfg.terminal.pool hq ((T).columns A_ (J_).sources) ((T).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "loaded" => input V cfg I_ R_ start head short literal
local notation "values" => portTable (G:=4) (V:=x.vertices) («M»:=M) (A:=x.arguments) («a»:=a) q
local notation "expr" => Book.expression (x.parts begin_)
local notation "out_" => x.afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "afterCode" => x.afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "afterTime" => x.afterSiteTime begin_ q grain peer old total modulo homes boundary


local notation "routeBase" => ({x.reachedRoutes begin_ rom q piece W K codes front peer old total modulo homes
  boundary cfg V other T with sources:=(J_).sources}:Input)
local notation "routerMem" => fun post:Memory w=>Suffix.events cfg plan_ (C_).layout ((A_).mount (loaded post))
private theorem column_le_bought (columns : Columns) (i : Fin 43) : size (columns i) ≤ wordsBought columns :=
  Finset.single_le_sum (f := fun j => size (columns j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A purchased width-factor column of the physical shelf and a whole row-arena band
lie successively below the final address. Thus both prefix counters fit a native word. -/
theorem reel_counter {w:ℕ} (space:last V cfg I_ R_ start<2^w) : cfg.terminal.rows+W<2^w := by
  have limits:=stages cfg I_ base_
  have rowEnd:cfg.terminal.rows≤(A_).finish:=by
    have stride:=(A_).stride_min
    change 2*cfg.sites+cfg.terminal.rows+cfg.packets+1<(A_).stride at stride
    change _ ≤ base_+22*(A_).stride
    omega
  have widthEnd:W≤wordsBought (I_).sources:=by
    have col : (I_).sources 29=.literal W:=rfl
    have leg : size ((I_).sources 29)≤wordsBought (I_).sources:=
      column_le_bought _ _
    rw [col] at leg
    exact (Nat.le_pow_clog (by decide) W).trans leg
  have room:takeOff cfg I_ base_ ≤ last V cfg I_ R_ start:=
    limits.2.2.1.trans (limits.2.2.2.1.trans limits.2.2.2.2)
  exact ((Nat.add_le_add (rowEnd.trans limits.1) widthEnd).trans room).trans_lt space

theorem reel_routes (m post:Memory w) (paid actors:Fin x.scalar.blocks→Bank)
    (boot:x.Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q grain≤x.literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space:last V cfg I_ R_ start<2^w) (rowCount:cfg.terminal.rows=x.paidRows)
    (allRows:cfg.terminal.rows=K*W) (wp:0<W)
    (fence firstFree dst:ℕ)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
    (late:dst<x.cohortEnd begin_) (ceiling:start≤fence)
    (countSide:total.base+total.size≤firstFree ∨ dst<total.base)
    (boundSide:boundary+(x.paidRows+1)≤firstFree ∨ dst<boundary)
    (moduloSide:modulo.base+modulo.size≤firstFree ∨ dst< modulo.base)
    (sites:Fin cfg.sites→Site) (f:∀i,DescentTerminalLocalPortBook.Room (sites i) 4 x.vertices M x.arguments)
    (labels:∀i,(sites i).Name ↪ Word a) (refs:∀i,(sites i).Arg→Word a)
    (perSite:∀i,(sites i).rows q≤W)
    (paidRows:purchased W (counts (q:=q) sites)≤cfg.terminal.rows)
    (book:Book.Issued (x.parts begin_) (fun i=>issue (sites i) (f i) (labels i) (refs i)) m)
    (countWords:∀j:Fin (Book.Bytes 4 x.vertices M x.arguments a),total.read m (j.val:Word w)=countTable q j)
    (boundaryWords:∀j:Fin (cfg.terminal.rows+1),m (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows).get j)
    (modWords:∀i:Fin cfg.terminal.rows,modulo.read m (i.val:Word w)=((i.val%W:ℕ):Word w)) :
    DescentTerminalRouteIssue.Reads (q:=q) (plan_).emit.route (rows (q:=q) (K₀:=K) sites wp f labels refs)
      (DescentTerminalEmitter.named cfg.terminal (plan_).emit (routerMem post)) := by
  have counter:=x.reel_counter begin_ rom q piece K codes front peer old total modulo homes boundary cfg V other space
  have positive:0<w:=by
    by_contra! bad
    have zero:w=0:=by omega
    rw [zero] at counter
    simp only [pow_zero] at counter
    omega
  have limits:=stages cfg I_ base_
  have room:(A_).finish<2^w := (limits.1.trans (limits.2.1.trans (limits.2.2.1.trans
    (limits.2.2.2.1.trans limits.2.2.2.2)))).trans_lt space
  have above:start≤base_:=by change start≤ start+_+_+_+_+_;omega
  have word:=above.trans_lt (((A_).start_le 22).trans_lt room)
  have early:=x.earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T x.vertices B paid actors boot romTop full space
  have receipt:=x.reel_route_books begin_ rom q piece K codes front peer old total modulo homes boundary
    cfg V other T hq head short m post paid actors boot word positive rowCount fence firstFree dst
    saved late ceiling countSide boundSide moduloSide _ book countWords boundaryWords modWords
  obtain ⟨l0,l1,l2,l3,l4,l5,l6,l7,l8⟩:=x.layers begin_
  have bound:boundary+(cfg.terminal.rows+1)≤base_:=by rw [rowCount];have:=boot.boundary;omega
  exact placed_route_columns V cfg routeBase R_ start head q V.roles V.privateWords V.nodes V.addresses
    grain x.vertices W hq short T (fun _ _=>0) post early space sites f labels refs wp perSite allRows
    paidRows counter bound receipt.1 receipt.2.1 receipt.2.2.1 receipt.2.2.2

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
