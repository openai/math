import OAI.Hierarchy.ProtocolRAMMenuAlphabetWords
import OAI.Hierarchy.ProbeDiscrepancyBoot
import OAI.Hierarchy.ProtocolRAMCalendarMenuSizes

namespace OAI
/-! # Resident packet recommendations and selector alphabet lengths on the public input tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.MenuROM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripDirectory DiscrepancyROM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N w : ℕ}
  (menu : Probe.FixedMenu F edge req box ε tree N)

/-- The actual scan computes the mixed-radix address from the observed digit
expressions and reads the committed packet's index from its installed page. -/
theorem packet_read {phases digits q goods : ℕ} (base radix : ℕ)
    (price : Fin phases→(Fin digits→Fin radix)→E→ℝ) (u : Fin phases)
    (b : Batch q goods) (quoted : Fin digits→Expr) (m : Memory w) (r : Word w)
    (key : Fin digits→Fin radix) (page : b.menu=(menus menu base radix price).bank u)
    (rad : b.radix=radix) (coordinates : b.quotes=List.ofFn quoted)
    (resident : (menus menu base radix price).Resident m)
    (read : ∀ i,(quoted i).eval m r=((key i).val:Word w)) :
    b.packet.eval m r=(recommendation menu (price u key):Word w) := by
  simp only [Batch.packet,menuLookup,Expr.eval,page,rad,coordinates,eval_menuKey m r quoted key read]
  exact resident u key

theorem packet_failed {phases digits q goods : ℕ} (base alphabet radix : ℕ)
    (price : Fin phases→(Fin digits→Fin radix)→E→ℝ) (u : Fin phases)
    (b : Batch q goods) (quoted : Fin digits→Expr) (m : Memory w) (r : Word w)
    (key : Fin digits→Fin radix) (page : b.menu=(menus menu base radix price).bank u)
    (rad : b.radix=radix) (coordinates : b.quotes=List.ofFn quoted)
    (terms : b.termCount=(alphabets menu alphabet).bank 0)
    (resident : (menus menu base radix price).Resident m) (alphabetReady : (alphabets menu alphabet).Resident m)
    (read : ∀ i,(quoted i).eval m r=((key i).val:Word w))
    (inside : price u key∈box) (failed : ε≤Probe.discrepancy F edge req (price u key)) :
    let j:=menu.select ⟨price u key,inside,failed⟩
    b.packet.eval m r=(((Fintype.equivFin menu.index j).val+1:ℕ):Word w) ∧
      b.termCount.read m (b.packet.eval m r)=((menu.packet j).terms:Word w) := by
  dsimp only
  have hit := packet_read menu base radix price u b quoted m r key page rad coordinates resident read
  rw [recommendation,dite_eq_left ⟨inside,failed⟩] at hit
  exact ⟨hit,by rw [hit,terms];exact alphabet_lookup menu alphabet m alphabetReady _⟩

variable {phases U V : ℕ}

/-- Two phase-indexed packet maps followed by the two true packet-alphabet
tables. The latter are shared over all calendar phases. -/
structure Pages (phases U V : ℕ) where
  left : Table phases U
  right : Table phases V
  leftAlphabet : Table 1 1
  rightAlphabet : Table 1 1

def Pages.stop (p : Pages phases U V) := p.rightAlphabet.stop

def Pages.words (p : Pages phases U V) (rest : Memory w) : Memory w :=
  both p.leftAlphabet p.rightAlphabet (both p.left p.right rest)

structure Pages.Ordered (p : Pages phases U V) : Prop where
  first : p.left.stop≤p.right.base
  second : p.right.stop≤p.leftAlphabet.base
  third : p.leftAlphabet.stop≤p.rightAlphabet.base

structure Pages.Resident (p : Pages phases U V) (m : Memory w) : Prop where
  left : p.left.Resident m
  right : p.right.Resident m
  leftAlphabet : p.leftAlphabet.Resident m
  rightAlphabet : p.rightAlphabet.Resident m

theorem Pages.resident (p : Pages phases U V) (rest : Memory w) (order : p.Ordered)
    (a : p.left.entries≤2^w) (b : p.right.entries≤2^w)
    (c : p.leftAlphabet.entries≤2^w) (d : p.rightAlphabet.entries≤2^w) : p.Resident (p.words rest) := by
  have lr := resident_both p.left p.right rest order.first a b
  have ab := resident_both p.leftAlphabet p.rightAlphabet (both p.left p.right rest) order.third c d
  have before : p.leftAlphabet.base≤p.rightAlphabet.base :=
    (Nat.le_add_right .. : p.leftAlphabet.base≤p.leftAlphabet.stop).trans order.third
  have unchanged (x : ℕ) (hx : x<p.leftAlphabet.base) :
      p.words rest x=both p.left p.right rest x :=
    (p.rightAlphabet.outside _ (.inl (hx.trans_le before))).trans (p.leftAlphabet.outside _ (.inl hx))
  have near : p.left.stop≤p.leftAlphabet.base :=
    order.first.trans ((Nat.le_add_right .. : p.right.base≤p.right.stop).trans order.second)
  exact ⟨lr.1.frame fun x _ hx=>unchanged x (hx.trans_le near),
    lr.2.frame fun x _ hx=>unchanged x (hx.trans_le order.second),ab.1,ab.2⟩

def Pages.base (p : Pages phases U V) := p.left.base

theorem Pages.frame (p : Pages phases U V) (rest : Memory w) (order : p.Ordered) (x : ℕ) (low : x<p.base) :
    p.words rest x=rest x := by
  have hx : x<p.left.stop := low.trans_le (Nat.le_add_right ..)
  have hy := hx.trans_le order.first
  have hz := (hy.trans_le (Nat.le_add_right .. : p.right.base≤p.right.stop)).trans_le order.second
  have hu := (hz.trans_le (Nat.le_add_right .. : p.leftAlphabet.base≤p.leftAlphabet.stop)).trans_le order.third
  exact (p.rightAlphabet.outside _ (.inl hu)).trans ((p.leftAlphabet.outside _ (.inl hz)).trans
    ((p.right.outside _ (.inl hy)).trans (p.left.outside _ (.inl low))))

end Hierarchy.ProtocolRAM.Calendar.MenuROM
end

end OAI
