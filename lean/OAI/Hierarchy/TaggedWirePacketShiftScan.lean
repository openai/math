import OAI.Hierarchy.TaggedWirePacketOpcode
import OAI.Hierarchy.TaggedWireAggregatePrefix

namespace OAI
/-! # The actual finite comparisons for the location of a paid subword in its gathered chord -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
variable {S n m t W : ℕ} {len : Fin n→ℕ}

namespace Operands
variable (o : Operands len) (ord : Fin t≃Σi,Fin (len i))

def priorAmount (i : Fin n) (j : Fin (len i)) (u : Fin t) : Expr :=
  let v:=ord u
  .branch .lt (o.edge v.1 v.2) (o.edge i j)
    (.branch .eq (o.endSite v.1 v.2 false) (o.endSite i j false)
      (.branch .eq (o.endSite v.1 v.2 true) (o.endSite i j true) (o.width v.1) (.lit 0)) (.lit 0)) (.lit 0)

def aggregateStart (i : Fin n) (j : Fin (len i)) : Expr :=
  PacketScan.earlier (fun _ : Fin t=>.lit 0) (o.priorAmount ord i j) (.lit 0) t

def matchingAmount (low high : Expr) (u : Fin t) : Expr :=
  let v:=ord u
  .branch .eq (o.endSite v.1 v.2 false) low
    (.branch .eq (o.endSite v.1 v.2 true) high (o.width v.1) (.lit 0)) (.lit 0)

/-- Active width of an arbitrary queried pair, even if absent from this
packet's paid-row directory. -/
def aggregateWidth (low high : Expr) : Expr :=
  PacketScan.earlier (fun _ : Fin t=>.lit 0) (o.matchingAmount ord low high) (.lit 0) t

end Operands

variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (ord : Fin t≃Σi,Fin (route i).length) (o : Operands fun i=>(route i).length)
    (mem : Memory W) (row : Word W) (read : Reads old edge route bits o mem row) (sites : S≤2^W) (rows : m≤2^W)
local notation "ids" => NativeSlot.edge route ord

theorem lt_select (a b yes no : Expr) {l r : ℕ} (la : a.eval mem row=(l : Word W))
    (hb : b.eval mem row=(r : Word W)) (lo : l<2^W) (hi : r<2^W) :
    (.branch .lt a b yes no : Expr).eval mem row=(if l<r then yes.eval mem row else no.eval mem row) := by
  have eq : ((l : Word W)<(r : Word W))↔l<r := by
    change (l : Word W).val<(r : Word W).val ↔ l<r
    rw [Fin.val_cast_of_lt lo,Fin.val_cast_of_lt hi]
  simp [Expr.eval,Comparison.test,la,hb,eq]

private def contribution (i : Fin n) (j : Fin (route i).length) (u : Fin t) : ℕ :=
  if (ids u).val<((route i).get j).val ∧ edge (ids u)=edge ((route i).get j) then bits (ord u).1 else 0

include read sites rows in
theorem prior_eval (i : Fin n) (j : Fin (route i).length) (u : Fin t) :
    (o.priorAmount ord i j u).eval mem row=(contribution edge route bits ord i j u : Word W) := by
  let r:=ids u
  let e:=(route i).get j
  have both : edge r=edge e ↔ (edge r).1.1.val=(edge e).1.1.val ∧ (edge r).1.2.val=(edge e).1.2.val := by
    constructor
    · intro same;rw [same];exact ⟨rfl,rfl⟩
    · rintro ⟨l,h⟩;exact Subtype.ext (Prod.ext (Fin.ext l) (Fin.ext h))
  unfold Operands.priorAmount contribution
  rw [lt_select mem row _ _ _ _ (read.key _ _) (read.key i j) (r.isLt.trans_le rows) (e.isLt.trans_le rows)]
  rw [PacketScan.eq_select mem row _ _ _ _ (read.low _ _) (read.low i j)
    ((edge r).1.1.isLt.trans_le sites) ((edge e).1.1.isLt.trans_le sites),
    PacketScan.eq_select mem row _ _ _ _ (read.high _ _) (read.high i j)
    ((edge r).1.2.isLt.trans_le sites) ((edge e).1.2.isLt.trans_le sites),read.width]
  change (if r.val<e.val then
    (if (edge r).1.1.val=(edge e).1.1.val then
      (if (edge r).1.2.val=(edge e).1.2.val then (bits (ord u).1 : Word W) else 0) else 0) else 0)=
    ((if r.val<e.val ∧ edge r=edge e then bits (ord u).1 else 0 : ℕ) : Word W)
  by_cases ahead : r.val<e.val <;> by_cases lo : (edge r).1.1.val=(edge e).1.1.val <;>
    by_cases hi : (edge r).1.2.val=(edge e).1.2.val <;> simp [both,ahead,lo,hi]

include read sites rows in
theorem aggregate_eval (i : Fin n) (j : Fin (route i).length) :
    (o.aggregateStart ord i j).eval mem row=(AggregatePrefix.paidShift route bits ord edge ((route i).get j) : Word W) := by
  let zero : Fin t→Fin 1:=fun _=>0
  have eq:=PacketScan.earlier_eval mem row (fun _ : Fin t=>.lit 0) (o.priorAmount ord i j) (.lit 0)
    zero (contribution edge route bits ord i j) 0 (Nat.two_pow_pos W) (fun _=>rfl)
    (prior_eval old edge route bits ord o mem row read sites rows i j) rfl t
  simpa [Operands.aggregateStart,NativeSlot.full,NativeSlot.mass,zero,AggregatePrefix.paidShift,contribution] using eq

include read sites in
theorem width_eval (low high : Expr) (ch : Chord S)
    (lower : low.eval mem row=(ch.1.1.val : Word W)) (upper : high.eval mem row=(ch.1.2.val : Word W)) :
    (o.aggregateWidth ord low high).eval mem row=(installedWidths edge (routeLoad route bits) ch : Word W) := by
  let amount : Fin t→ℕ:=fun u=>if edge (ids u)=ch then bits (ord u).1 else 0
  have same (z : Chord S) :
      z=ch ↔ z.1.1.val=ch.1.1.val ∧ z.1.2.val=ch.1.2.val := by
    constructor
    · rintro rfl;exact ⟨rfl,rfl⟩
    · rintro ⟨l,h⟩;exact Subtype.ext (Prod.ext (Fin.ext l) (Fin.ext h))
  have pay (u : Fin t) : (o.matchingAmount ord low high u).eval mem row=(amount u : Word W) := by
    let c:=edge (ids u)
    rw [Operands.matchingAmount,PacketScan.eq_select mem row _ _ _ _ (read.low _ _) lower
      (c.1.1.isLt.trans_le sites) (ch.1.1.isLt.trans_le sites)]
    rw [PacketScan.eq_select mem row _ _ _ _ (read.high _ _) upper
      (c.1.2.isLt.trans_le sites) (ch.1.2.isLt.trans_le sites),read.width]
    change (if c.1.1.val=ch.1.1.val then
        (if c.1.2.val=ch.1.2.val then (bits (ord u).1 : Word W) else 0) else 0)=
      ((if c=ch then bits (ord u).1 else 0 : ℕ) : Word W)
    by_cases lo : c.1.1.val=ch.1.1.val <;> by_cases hi : c.1.2.val=ch.1.2.val <;>
      simp [same c,lo,hi]
  have eq:=PacketScan.earlier_eval mem row (fun _ : Fin t=>.lit 0) (o.matchingAmount ord low high) (.lit 0)
    (fun _ : Fin t=>(0 : Fin 1)) amount 0 (Nat.two_pow_pos W) (fun _=>rfl) pay rfl t
  rw [←AggregatePrefix.chordTotal_eq_width route bits ord edge ch]
  simpa [Operands.aggregateWidth,NativeSlot.full,NativeSlot.mass,amount,AggregatePrefix.chordTotal] using eq

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
