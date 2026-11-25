import OAI.Hierarchy.DescentTerminalPreflightPorts
import OAI.Hierarchy.DescentTerminalPreflightMeasured

namespace OAI
/-! # Real source intervals retained by the late exterior reel and history fold -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentTerminalVertexFields DescentTerminalCompiledPrefix DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalDenseHeaderBoot DescentTerminalPrimitiveFrames
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem kept_bank {w : ℕ} (m o : Memory w) (fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→ o a=m a) (b : Bank)
    (top : b.base+b.size≤fence) (location : b.base+b.size≤firstFree ∨ dst<b.base)
    (u : Word w) : b.read o u=b.read m u := by
  apply saved
  · exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le top
  · rcases location with h|h
    · exact .inl ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le h)
    · exact .inr (h.trans_le (Nat.le_add_right ..))

private theorem kept_widths {w : ℕ} (m o : Memory w) (q grain rom fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→ o a=m a) (widths : Bank)
    (romTop : rom+extent q grain≤fence) (romSide : rom+extent q grain≤firstFree ∨ dst<rom)
    (widthTop : widths.base+widths.size≤fence) (widthSide : dst<widths.base) :
    ∀i u,(sources q grain rom widths i).read o u=(sources q grain rom widths i).read m u := by
  have table (i : Fin 4) :=
    kept_bank m o fence firstFree dst saved (bank q grain rom i)
      ((cell_end q grain rom i).trans romTop)
      (romSide.imp ((cell_end q grain rom i).trans ·) (·.trans_le (Nat.le_add_right ..)))
  intro i
  fin_cases i
  · exact kept_bank m o fence firstFree dst saved widths widthTop (.inr widthSide)
  · exact table 0
  · exact table 1
  · exact table 2
  · exact table 3

variable (x : Spec) (begin_ rom q piece W K codes front : ℕ) (peer : Bank)
    (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank) (total modulo homes : Bank) (boundary : ℕ)
    (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format) (other : Input) (T : RouteSources.Tables)
    (vertices B : ℕ)
local notation "grain" => W*piece
local notation "I_" => x.reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other T vertices B
local notation "P_" => x.cables begin_ peer old
local notation "U_" => x.publicWidths begin_
local notation "start" => x.maskBase begin_
local notation "lit" => x.literalBase begin_

/-- The history-fold program may overwrite the measured flags in its reserved
scratch interval. Every header and width source lies in a disjoint interval. -/
theorem reel_ports {w : ℕ} (m o : Memory w) (fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→ o a=m a)
    (late : dst<x.cohortEnd begin_) (ceiling : start≤fence)
    (romTop : rom+extent q grain≤lit) (romSide : rom+extent q grain≤firstFree ∨ dst<rom) :
    (∀j,lit≤j→j<start→ o j=m j) ∧
    (∀i u,((I_).cable i).read o u=((I_).cable i).read m u) ∧
    (∀i u,((I_).exterior i).read o u=((I_).exterior i).read m u) := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.layers begin_
  have low : lit≤fence := by omega
  have table := kept_widths m o q grain rom fence firstFree dst saved
  have bound := x.ports_before begin_ rom q grain peer old total modulo homes boundary cfg other romTop
  have privateLo : dst<(P_).printer.origin := by
    have gaps := (P_).gaps
    have startP : (x.controls begin_).finish≤(P_).base := gaps.1
    have beforeP := gaps.2.1
    have belowP : (P_).slab≤(P_).population.base := Nat.le_add_right ..
    have toP := gaps.2.2.1
    omega
  have publicLo : dst<(U_).widthLayout.origin := by
    change dst<x.cableEnd begin_+_+_
    omega
  have output {l : DescentTerminalWidthRowsRAM.Layout} (before : dst<l.origin) : dst<l.output.base :=
    before.trans_le ((Nat.le_add_right l.origin l.entries).trans (Nat.le_add_right l.prefix.base l.prefix.size))
  refine ⟨fun j jlo jhi=>saved j (jhi.trans_le ceiling) (.inr (by omega)),?_,?_⟩
  · exact table (P_).printer.output (romTop.trans low) romSide ((bound.1 0).trans low) (output privateLo)
  · exact table (U_).widthLayout.output (romTop.trans low) romSide ((bound.2 0).trans low) (output publicLo)

/-- Six Book inputs, their six coefficient pages, and the eight acquired
directory tapes are all past the early scratch. The count and boundary ROMs
can be on either side of it. -/
theorem reel_control_ranges {w : ℕ} (m o : Memory w) (fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→ o a=m a)
    (late : dst<x.cohortEnd begin_) (ceiling : start≤fence)
    (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors old peer total modulo homes boundary)
    (rows : cfg.terminal.rows=x.paidRows)
    (countSide : total.base+total.size≤firstFree ∨ dst<total.base)
    (boundSide : boundary+(x.paidRows+1)≤firstFree ∨ dst<boundary) :
    (∀i u,(((I_).parts i).source.read o u=((I_).parts i).source.read m u) ∧
          (((I_).parts i).weights.read o u=((I_).parts i).weights.read m u)) ∧
    (∀j u,((I_).directory j).read o u=((I_).directory j).read m u) ∧
    (∀u,(I_).totals.read o u=(I_).totals.read m u) ∧
    (∀i : Fin (cfg.terminal.rows+1),o ((I_).boundaries+i.val)=m ((I_).boundaries+i.val)) := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.layers begin_
  have hi : (x.controls begin_).finish≤fence := by omega
  have low : dst<x.weights begin_ := by omega
  have src (j : Fin 6) : x.bookBegin begin_≤((x.parts begin_ j).source).base := by
    change x.bookBegin begin_≤x.bookBegin begin_+_+_+_+_
    exact (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have weight (j : Fin 6) : x.weights begin_≤((x.parts begin_ j).weights).base := Nat.le_add_right ..
  have dir (j : Fin 8) : x.weights begin_≤(x.directory begin_ j).base := by
    have book : x.weights begin_≤x.bookEnd begin_ := c.trans d
    have src₁ := c.trans (src 1)
    fin_cases j
    · change x.weights begin_≤x.bookEnd begin_+_;omega
    · exact src₁
    · change x.weights begin_≤x.bookEnd begin_+_+_;omega
    · change x.weights begin_≤x.bookEnd begin_+_+_+_;omega
    all_goals change x.weights begin_≤x.bookEnd begin_+_+_+_+1+_;omega
  have parts (j : Fin 6) := x.book_banks begin_ j
  refine ⟨fun j u=>⟨kept_bank m o _ _ _ saved _ ((parts j).1.trans (by omega)) (.inr (low.trans_le (c.trans (src j)))) u,
    kept_bank m o _ _ _ saved _ ((parts j).2.trans (by omega)) (.inr (low.trans_le (weight j))) u⟩,
    fun j=>kept_bank m o _ _ _ saved _ ((DescentTerminalControlProgram.early_before
      (x.controls begin_) (x.parts begin_) (parts 1).1 j).trans hi) (.inr (low.trans_le (dir j))),
    kept_bank m o _ _ _ saved _ (boot.total.trans (by omega)) countSide,?_⟩
  intro ix
  have lim : ix.val<x.paidRows+1 := by simpa only [rows] using ix.isLt
  have top := boot.boundary
  exact saved _ (by change boundary+ix.val<fence;omega)
    (by change boundary+ix.val<firstFree ∨ dst<boundary+ix.val;omega)

/-- All nine families lie between the original census and the Book weights.
The post-reel read therefore gives the same complete tuple at every site. -/
theorem reel_measured {w : ℕ} (head : ℕ) (short : vertices*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords
    V.nodes V.addresses V.piece≤B) (literal : DescentTerminalEmitter.Compact.Literals (I_).sources)
    (m o : Memory w) (fence firstFree dst : ℕ)
    (saved : ∀a,a<fence→(a<firstFree ∨ dst<a)→ o a=m a)
    (late : dst<x.cohortEnd begin_) (ceiling : start≤fence)
    (early : Earlier cfg I_ (afterMeter V cfg (x.channels begin_) start) (meter V (x.channels begin_) start).layout w)
    (room : last V cfg I_ (x.channels begin_) start<2^w) {shops : ℕ} (i : Fin shops) :
    let R:=x.channels begin_
    let cpu:=meter V R start
    let base:=afterMeter V cfg R start
    let regs:=registers V cfg R start head
    let runAt:=fun e : Memory w=>Suffix.sockets cfg (AddressPlan.layout cfg I_ base regs)
      ((rowArena cfg I_ base).mount (input V cfg I_ R start head short literal e))
    let view:=fun e : Memory w=>measured (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
      (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) cpu.layout (runAt e) i
    view o=view m := by
  dsimp only
  rw [sockets_measured V cfg I_ (x.channels begin_) start head short literal o early room (x.channels_before begin_),
      sockets_measured V cfg I_ (x.channels begin_) start head short literal m early room (x.channels_before begin_)]
  funext f
  have at_ := kept_bank m o fence firstFree dst saved ((x.channels begin_).bank f)
    ((x.channels_before begin_ f).trans ceiling) (.inr (late.trans_le (x.channels_after_cohorts begin_ f))) (i.val:Word w)
  simp only [measured,show (meter V (x.channels begin_) start).layout.channel f=(x.channels begin_).bank f from rfl,at_]

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
