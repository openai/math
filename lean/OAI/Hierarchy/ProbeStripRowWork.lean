import OAI.Hierarchy.ProbeStripPortBoard
import OAI.Hierarchy.ProbeStripFormat
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost

namespace OAI
/-! # Work of the original selector, alphabet, stock and printed wire in a padded strip -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage Calendar
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical

variable {F E A D : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] [Fintype D]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N z d k q : ℕ}

structure RowWork {n : ℕ} (B : Repair q n) (u : ℕ) : Prop where
  packet : B.batch.packet.work≤u
  owner : B.batch.owner.work≤u
  fields : ∀j,(B.batch.field j).work≤u
  stocks : ∀j,(B.batch.stock j).work≤u
  prices : ∀j,(B.batch.perCopy j).work≤u
  wires : ∀i j,(B.wire i j).work≤u
  report : ∀j,(B.reportWidth j).work≤u
  quotes : ∀e∈B.batch.quotes,e.work≤u
  digits : B.batch.quotes.length≤u
  maximum : B.batch.maxWidth≤u

private theorem mul_limited (u : ℕ) (x y : Expr) (hx : x.work≤u) (hy : y.work≤u)
    (n : ℕ) (hn : n≤u) :
    (boundedMul n x y).work ≤ 1+n*(u+3+u*(u+1)) := by
  induction n with
  | zero => simp [boundedMul,Expr.work]
  | succ n ih =>
    have old := ih (Nat.le_of_succ_le hn)
    have scaleBound : (n+1)*(x.work+1) ≤ u*(u+1) :=
      Nat.mul_le_mul hn (Nat.add_le_add_right hx 1)
    change y.work+1+(scale (n+1) x).work+(boundedMul n x y).work+1 ≤ _
    rw [scale_work, Nat.succ_mul n (u+3+u*(u+1))]
    omega

def entryWork (u : ℕ) := 1+u*(u+3)
def operandWork (u : ℕ) := u+entryWork u+10

def stripWork (u : ℕ) :=
  let t:=operandWork u
  20+t+(1+t*(t+3+t*(t+1)))+(1+u*(u+entryWork u+2))+3*u

theorem placed_row_work (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (b : Boards z d k q (Fintype.card D) (Fintype.card E)) (market : Market z d k)
    (dim header u : ℕ) (arity : q≤u) (codes : Fintype.card m.index≤u) (ports : Fintype.card E≤u)
    (digits : Fintype.card D≤u) (maximum : b.maxWidth≤u) (report : b.report.work≤u)
    (coordinate : ∀i,(c.address i).work≤u)
    (testWork :
      let old : Bank := {b.old with base:=market.shelf.stockBase}
      let t:=tested {b.test with live:=c.live,rows:=market.rows,population:=2^z}
        b.price (GlobalTests.offsets b.globalTests) old c.digit
      t.failure.test.work≤u ∧ ∀i,(t.quoted i).work≤u) :
    let raw:=format c m market b.repair b.test b.globalTests b.baseline b.price b.terms b.menu
      b.enabled b.selectors b.old b.reserve b.half b.cash .row b.report b.priceOut b.copies
      b.maxWidth b.start b.indexBits b.limit
    RowWork (PortPadding.format dim header c.slot raw).board (stripWork u) := by
  intro raw
  let f:=PortPadding.format dim header c.slot raw
  let bank : Bank := {b.old with base:=market.shelf.stockBase}
  let t:=tested {b.test with live:=c.live,rows:=market.rows,population:=2^z}
    b.price (GlobalTests.offsets b.globalTests) bank c.digit
  let port : Fin (Fintype.card E)→E := (Fintype.equivFin E).symm
  let real:=batch (q:=q) m t b.terms b.menu f.board.repairBits b.selectors bank
    .row b.copies b.maxWidth port c.slot
  have packet : real.packet.work≤u := by
    have limit : t.failure.test.work≤u := testWork.1
    change (menuLookup b.menu t.radix (List.ofFn t.quoted)).work≤u
    simp only [StripTest.failure,FailureWords.test,FailureWords.effective,menuLookup,Expr.work] at limit ⊢
    omega
  have entries (term : m.index→ℕ) : (entry m real.packet term).work≤entryWork u := by
    let options (i : Fin (Fintype.card m.index)) := Expr.lit (term ((Fintype.equivFin m.index).symm i))
    have each (i : Fin (Fintype.card m.index)) : (options i).work ≤ 1 := le_rfl
    apply (BoughtSockets.choose_work_bound (Fintype.card m.index) 1 1 options real.packet each).trans
    exact Nat.add_le_add_left (Nat.mul_le_mul codes (by omega)) 1
  let t₁:=operandWork u
  have total : stripWork u =
      20+t₁+(1+t₁*(t₁+3+t₁*(t₁+1)))+(1+u*(u+entryWork u+2))+3*u := rfl
  have lu : u≤t₁ := by dsimp only [t₁,operandWork]; omega
  have ed : entryWork u≤t₁ := by dsimp only [t₁,operandWork]; omega
  have one : 1≤t₁ := by dsimp only [t₁,operandWork]; omega
  have mul (e : Fin (Fintype.card E)) :
      (real.need e).work ≤ 1+t₁*(t₁+3+t₁*(t₁+1)) := by
    have r := (entries (fun i=>useBits m i (port e))).trans ed
    exact (mul_limited t₁ (.lit b.copies) (real.perCopy e) one r b.maxWidth (maximum.trans lu)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (maximum.trans lu)) 1)
  have stock (e : Fin (Fintype.card E)) : (real.stock e).work≤ stripWork u := by
    change (inventory bank (real.need e) (c.slot e)).work≤_
    unfold Channels.slot
    cases h : c.account ((Fintype.equivFin E).symm e) with
    | none =>
      have h:=mul e
      change (real.need e).work≤_
      rw [total]
      omega
    | some a =>
      change (c.address a).work+5≤_
      have h:=coordinate a
      rw [total]
      omega
  have wire (e : Fin (Fintype.card E)) (j : Fin q) :
      (wires m real port e j).work≤entryWork u := entries _
  have enough : t₁≤ stripWork u := by rw [total]; omega
  have pad {α : Type} (x : Fin (Fintype.card E)→α) (y : α) (P : α→Prop)
      (hx : ∀i,P (x i)) (hy : P y) (i : Fin dim) : P (PortPadding.extend x y i) := by
    unfold PortPadding.extend
    split <;> first | exact hx _ | exact hy
  constructor
  · exact packet.trans (lu.trans enough)
  · change 2≤ stripWork u; rw [total]; omega
  · intro j
    change (WireTelescope.HistogramShelf.field b.selectors j).work≤_
    simp only [WireTelescope.HistogramShelf.field,Expr.work,scale_work]
    rw [total]
    omega
  · intro i
    exact pad real.stock (Expr.lit 0) (fun e : Expr=>e.work≤ stripWork u) stock (one.trans enough) i
  · intro i
    exact pad real.perCopy (Expr.lit 0) (fun e : Expr=>e.work≤ stripWork u)
      (fun j=>(entries (fun code => useBits m code (port j))).trans (ed.trans enough))
      (one.trans enough) i
  · intro i j
    exact pad (wires m real port) (fun _ : Fin q=>Expr.lit 0) (fun tab : Fin q→Expr=>(tab j).work≤ stripWork u)
      (fun i=>(wire i j).trans (ed.trans enough)) (one.trans enough) i
  · intro j
    apply (BoughtSockets.choose_work_bound (Fintype.card E) 0 (entryWork u) _ _ (fun i=>wire i j)).trans
    have est := Nat.mul_le_mul ports (Nat.add_le_add_right (Nat.add_le_add_right report (entryWork u)) 2)
    rw [total]
    omega
  · exact fun e he=>by
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
      exact (testWork.2 i).trans (lu.trans enough)
  · change (List.ofFn t.quoted).length≤_
    simpa only [List.length_ofFn] using digits.trans (lu.trans enough)
  · exact maximum.trans (lu.trans enough)

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
