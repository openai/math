import OAI.Hierarchy.DescentTerminalPreflightEarlier
import OAI.Hierarchy.DescentTerminalPreflightChronology
import OAI.Hierarchy.DescentTerminalIncomingBooks

namespace OAI
/-! # Six-column input records and the three allocator tables after the final exterior reel -/
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
local notation "a" => Book.tokenBits (x.vertices*x.arguments)
local notation "M" => x.vertices*x.arguments
variable {w:ℕ} (hq:0<q)
variable (head : ℕ) (short : x.vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ x.pageBits)
local notation "literal" => ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses grain x.vertices W B
  cfg.terminal.pool hq (T.columns A_ (J_).sources) (T.value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "loaded" => input V cfg I_ R_ start head short literal
local notation "values" => portTable (G:=4) (V:=x.vertices) («M»:=M) (A:=x.arguments) («a»:=a) q
local notation "expr" => Book.expression (x.parts begin_)
local notation "out_" => x.afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "afterCode" => x.afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "afterTime" => x.afterSiteTime begin_ q grain peer old total modulo homes boundary

theorem reel_route_books (m post:Memory w) (paid actors:Fin x.scalar.blocks→Bank)
    (boot:x.Before begin_ paid actors old peer total modulo homes boundary)
    (space:start<2^w) (positive:0<w) (rowCount:cfg.terminal.rows=x.paidRows)
    (fence firstFree dst:ℕ)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
    (late:dst<x.cohortEnd begin_) (ceiling:start≤fence)
    (countSide:total.base+total.size≤firstFree ∨ dst<total.base)
    (boundSide:boundary+(x.paidRows+1)≤firstFree ∨ dst<boundary)
    (moduloSide:modulo.base+modulo.size≤firstFree ∨ dst< modulo.base)
    (tape:Fin cfg.sites→Book 4 x.vertices M x.arguments a)
    (book:Book.Issued (x.parts begin_) tape m)
    (countWords:∀j:Fin (Book.Bytes 4 x.vertices M x.arguments a),total.read m (j.val:Word w)=countTable q j)
    (boundaryWords:∀j:Fin (cfg.terminal.rows+1),m (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows).get j)
    (modWords:∀i:Fin cfg.terminal.rows,modulo.read m (i.val:Word w)=((i.val%W:ℕ):Word w)) :
    Book.Issued (x.parts begin_) tape (loaded post) ∧
    (∀j:Fin (Book.Bytes 4 x.vertices M x.arguments a),total.read (loaded post) (j.val:Word w)=countTable q j) ∧
    (∀j:Fin (cfg.terminal.rows+1),(loaded post) (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows).get j) ∧
    (∀i:Fin cfg.terminal.rows,modulo.read (loaded post) (i.val:Word w)=((i.val%W:ℕ):Word w)) := by
  let site:=(X_).after values expr m
  let ports:=out_ site
  obtain ⟨l0,l1,l2,l3,l4,l5,l6,l7,l8⟩:=x.layers begin_
  have origin:x.cohortEnd begin_≤x.bookEnd begin_:=l0.trans (l1.trans (l2.trans l3))
  have controlBefore:(X_).finish ≤ start:=l5.trans (l6.trans (l7.trans l8))
  have before:x.bookEnd begin_≤ start:=l4.trans controlBefore
  have fit (b:Bank) (end_:b.base+b.size≤x.bookEnd begin_): b.Fits w (x.bookEnd begin_):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt (before.trans_lt space)),end_⟩
  have source (j:Fin 6):((x.parts begin_) j).fetch.Fits w (x.bookEnd begin_):=
    ⟨fit _ ((x.book_banks begin_ j).2.trans l3),fit _ (x.book_banks begin_ j).1,trivial⟩
  have exprOK:(expr).Fits w (x.bookEnd begin_):=⟨source 0,source 1,source 2,source 3,source 4,source 5⟩
  have aStep:=(X_).any m values expr exprOK (controlBefore.trans_lt space)
  have four:=x.after_site_run begin_ q grain peer old total modulo homes boundary site paid actors boot space positive
  have pre (u:ℕ) (h:u<x.bookEnd begin_):ports u=m u:=
    (four.2.2 _ (h.trans_le l4)).trans (aStep.2.2 _ (.inl h))
  have lowBank (b:Bank) (end_:b.base+b.size≤x.bookEnd begin_) (u:Word w):b.read ports u=b.read m u:=
    pre _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le end_)
  have kept (b n j:ℕ) (first:b≤j) (inside:j<b+n) (end_:b+n≤x.bookEnd begin_)
      (side:b+n≤firstFree ∨ dst<b):post j=ports j:=by
    apply saved j (inside.trans_le (end_.trans (before.trans ceiling)))
    rcases side with left|right
    · exact .inl (inside.trans_le left)
    · exact .inr (right.trans_le first)
  have keepBank (b:Bank) (end_:b.base+b.size≤x.bookEnd begin_)
      (side:b.base+b.size≤firstFree ∨ dst<b.base) (u:Word w):b.read post u=b.read m u:=
    (kept b.base b.size _ (Nat.le_add_right ..)
      (Nat.add_lt_add_left (Nat.mod_lt u.val (Nat.two_pow_pos _)) _) end_ side).trans (lowBank b end_ u)
  have src (j:Fin 6):x.bookBegin begin_≤((x.parts begin_ j).source).base:=by
    change x.bookBegin begin_≤x.bookBegin begin_+_+_+_+_
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have weight (j:Fin 6):x.weights begin_≤((x.parts begin_ j).weights).base:=Nat.le_add_right ..
  have parts' : Book.Issued (I_).parts tape post :=
    ⟨fun i j=>(keepBank _ (x.book_banks begin_ j).1 (.inr (late.trans_le (l0.trans (l1.trans (l2.trans (src j)))))) _).trans (book.source i j),
     fun j u=>(keepBank _ ((x.book_banks begin_ j).2.trans l3) (.inr (late.trans_le (l0.trans (l1.trans (weight j))))) _).trans (book.values j u)⟩
  have boundaryEnd:boundary+(cfg.terminal.rows+1)≤x.bookEnd begin_:=by rw [rowCount];exact boot.boundary.trans origin
  have modEnd:=boot.modulo.trans origin
  have keepBoundary (i:Fin (cfg.terminal.rows+1)):post (boundary+i.val)=m (boundary+i.val):=
    (kept _ _ _ (Nat.le_add_right ..) (Nat.add_lt_add_left i.isLt _) boundaryEnd (rowCount.symm ▸ boundSide)).trans
      (pre _ ((Nat.add_lt_add_left i.isLt _).trans_le boundaryEnd))
  apply incoming_books V cfg I_ R_ start head short literal post tape
    (fun j=>⟨(x.book_banks begin_ j).1.trans before,((x.book_banks begin_ j).2.trans l3).trans before⟩)
    ((boot.total.trans origin).trans before) (boundaryEnd.trans before) (modEnd.trans before) parts'
  · exact fun j=>(keepBank _ (boot.total.trans origin) countSide _).trans (countWords j)
  · exact fun j=>(keepBoundary j).trans (boundaryWords j)
  · exact fun i=>(keepBank _ modEnd moduloSide _).trans (modWords i)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
