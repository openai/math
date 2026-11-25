import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteReceipt
import OAI.Computability.BorderVNP.FiniteEvaluatorPreparedTeam
import OAI.Computability.BorderVNP.FiniteEvaluatorPaddingField
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseProgram

/-! # Exact field contraction after the distributed routing return

The genuine installer and owned-group paths exhaust the private words over
the received common broadcast. Their local continuation clocks begin at the
actual returned memory. An unused slot with a nonzero end kills its whole
team product. On the remaining paths, the local validators and the scalar
calls compute the corresponding public word's field value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout.SignedRouteReceipt

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open Padding.Banks NativeIntervals FiniteEvaluator RoutingISA VPVNP.BurstRAM
open scoped BigOperators Classical

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable {V : FieldRawLayout L S} {R : ℕ} {raw : V.Raw R} {codec : Cells.Codec} (a : SignedRouteReceipt V R raw codec)

local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "group" => V.owners R (Sigma.fst (Prod.fst raw))
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis group
local notation "Choice" => CubeTriple.Fiber (Sigma.snd (Prod.fst raw))
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock (SignedRouteReceipt.length a)

/-- One genuine return of the installed field deck and owned-group traversal per team. -/
abbrev Returns := (u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups a.table)
  (a.pub u) a.macros (a.regs u) (a.original u)

/-- The returned physical history for a particular private assignment, including
the actual choice bits, charged local clock, signed input addresses and native bank words. -/
structure Reached (f : Choice) (paths : a.Returns) : Prop where
  trace : ∀ u, DiagonalResidueRAM.TraceOK (paths u).val.1 (((enc f.val).2 u).val) (paths u).val.1.length
  cost : ∀ u, traceCost (paths u).val.1 ≤ (CubeDeck.install a.table).slots+
    V.ownedTicks R raw a.header a.profile a.cells a.cables a.maxRows a.stride a.pub u
  prepared : ∀ u, CubePacket.Prepared (a.inputs f u) (a.pub u) (paths u).val.2.2
  sources : ∀ u, CubePacket.Sources (a.inputs f u) (a.signedArena.tasks u.val (readings (a.pub u) 0) (a.offsets u) (a.control u))
  views : ∀ u x, group (x.row axis).1=u →
    (V.bankData R (V.withPrivate R raw f) a.arena.header.packetBase a.arena.singleBank).Holds (paths u).val.2.2 x

variable (interval : NativeIntervals.Layout) (dir : ℕ → ℕ)
variable (paths : a.Returns)
local notation "ram" => fun u : Fin (R+1) => Prod.snd (Prod.snd (Subtype.val (paths u)))
local notation "pad" => fun u : Fin (R+1) => Padding.Layout.fromFrame (Fin.val (SignedRouteReceipt.pub a u 0)) (readings (ram u))

/-- Input words checked by the padding guards even on rejecting paths. They
are independent of the existence of a passing report or cell-call continuation. -/
structure PaddingReads where
  /-- Actual inputs of the four opening instructions at each team. -/
  stage : Fin (R+1) → OpenSuffix.Inputs
  ready : ∀ u, OpenSuffix.Ready (stage u) (a.pub u 0).val (readings (ram u)) a.w
  packets : ∀ u, (pad u).packets=a.arena.header.packetBase
  singles : ∀ u, (pad u).singles=a.arena.singleBank
  header : ∀ u, Padding.TailHeader axis group Fin.valEmbedding u (pad u) (readings (ram u))
    (fun j => dir (interval.widths+j)) L.blocks L.bitWidth L.copies L.alternatives L.supply

variable {row : Fin L.count ↪o Fin interval.count} {cells : L.Cell ↪ ℕ} {hz : L.alphabet^(L.dimension+1)=interval.alphabet}
variable {before : ℕ → ℕ}
variable (physical : PhysicalRows N L.cell interval before L.order row cells L.label (productCode L.dimension L.alphabet interval.alphabet hz))
variable (widths : interval.Image before interval.count dir)
variable (bank : Ports bits) (prep : Code)

local notation "assembled" => Code.seq (openCells (SignedRouteReceipt.table a)) (Code.seq prep privateReturns)

/-- Native per-team source records required only once every unused bit of the
recovered public assignment passes. The record carries the report-path
bijection, operand reads, call budgets and finite field labels. -/
noncomputable abbrev TeamPreparation (f : Choice) (u : Fin (R+1)) :=
  OwnedContinuation.PreparedTeam V R (V.withPrivate R raw f) bank (V.publicFiberEquiv R raw f).val u
    a.header a.profile a.cells a.cables a.maxRows a.stride a.table a.params codec prep (a.pub u)
    (paths u).val.2.1 (paths u).val.2.2 a.length (a.ticks u-traceCost (paths u).val.1) a.burst a.clock

include physical widths in
/-- The product at this reached native family is the public word's value,
including vanishing when a nonzero padded end fails at its responsible team. -/
theorem private_product (f : Choice) (reach : a.Reached f paths) (head : a.PaddingReads interval dir paths) (hw : 0<a.w)
    (passing : FieldSiteDirectory.pinsPass L (V.owners R) (V.withPrivate R raw f).1 →
      ∀ u, Nonempty (a.TeamPreparation paths bank prep f u)) :
    (∏ u, boundedWeight (a.pub u) lib ret fuel (OwnedContinuation.codeFor prep) (paths u).val.2.1 (paths u).val.2.2
      (a.ticks u-traceCost (paths u).val.1) a.burst a.clock)=V.publicValue R bank (V.publicFiberEquiv R raw f).val := by
  let next := V.withPrivate R raw f
  let z := (V.publicFiberEquiv R raw f).val
  have decode : V.readPublic R z=next.1 := V.readPublic_fiber R raw f
  have seen (u : Fin (R+1)) (v : View L.dimension L.alphabet L.blocks (L.copies*L.bitWidth))
      (owns : group (v.row axis).1=u) : (V.bankData R next (pad u).packets (pad u).singles).Holds (ram u) v := by
    rw [head.packets u,head.singles u]
    exact reach.views u v owns
  have guards := V.padding_valid_iff R next physical widths a.pub ram hw seen head.header
  rw [V.public_eq_owned R a.table a.fixed bank z,decode]
  by_cases ok : FieldSiteDirectory.pinsPass L (V.owners R) next.1
  · rw [ite_eq_left ok]
    apply Finset.prod_congr rfl
    intro u _
    obtain ⟨team⟩ := passing ok u
    exact team.passing_public a.fixed decode (reach.prepared u) ((guards.mpr ok) u)
  · rw [ite_eq_right ok]
    obtain ⟨u,fail⟩ := not_forall.mp (mt guards.mp ok)
    exact Finset.prod_eq_zero (Finset.mem_univ u) (OwnedContinuation.rejected_stage (F:=F) (a.pub u) a.length
      (paths u).val.2.1 (paths u).val.2.2 codec prep (head.stage u) (head.ready u) (a.ticks u-traceCost (paths u).val.1)
      a.burst a.clock fail)

/-- Reindex the complete reached history family by the accepted word fiber.
The attained prefix certifies the exact memory and residual clock at each team. -/
theorem sum_reached
    (localValue : ∀ f (h : a.Returns), a.Reached f h →
      (∏ u, boundedWeight (a.pub u) lib ret fuel (OwnedContinuation.codeFor prep) (h u).val.2.1 (h u).val.2.2
        (a.ticks u-traceCost (h u).val.1) a.burst a.clock)=V.publicValue R bank (V.publicFiberEquiv R raw f).val) :
    letI := Fintype.ofEquiv _ (V.publicFiberEquiv R raw)
    (∏ u, boundedWeight (a.pub u) lib ret fuel assembled (a.regs u) (a.original u) (a.ticks u) a.burst a.clock)=
      ∑ z : V.PublicFiber R raw, V.publicValue R bank z.val := by
  let := Fintype.ofEquiv _ (V.publicFiberEquiv R raw)
  obtain ⟨E,actual,value⟩ := a.product_stage prep
  rw [value]
  refine (Finset.sum_congr rfl fun f _ => ?_).trans ((V.publicFiberEquiv R raw).sum_comp (fun z => V.publicValue R bank z.val))
  have cut := (actual f).1
  exact localValue f (E f) ⟨fun u => (cut u).1,fun u => (cut u).2.1,fun u => (cut u).2.2.1,
    fun u => (cut u).2.2.2.1,fun u => (cut u).2.2.2.2⟩

include physical widths in
/-- The all-team field weight of the remaining actual native program is the
sum over exactly the checked public words with this declaration and these
transmitted common lists. The theorem applies to the executed preparation
code and its selected slot-zero decoder. -/
theorem value_stage (hw : 0<a.w)
    (padding : ∀ f (h : a.Returns), a.Reached f h → Nonempty (a.PaddingReads interval dir h))
    (passing : ∀ f (h : a.Returns), a.Reached f h → FieldSiteDirectory.pinsPass L (V.owners R) (V.withPrivate R raw f).1 →
      ∀ u, Nonempty (a.TeamPreparation h bank prep f u)) :
    letI := Fintype.ofEquiv _ (V.publicFiberEquiv R raw)
    (∏ u, boundedWeight (a.pub u) lib ret fuel assembled (a.regs u) (a.original u) (a.ticks u) a.burst a.clock)=
      ∑ z : V.PublicFiber R raw, V.publicValue R bank z.val := by
  apply a.sum_reached bank prep
  intro f h reached
  obtain ⟨head⟩ := padding f h reached
  exact a.private_product interval dir h physical widths bank prep f reached head hw (passing f h reached)

include physical widths in
/-- On the program's actual entry point the chosen cell decoder fixes its
preparation instructions. In particular, the sparse driver uses its native
fragment collection, bucketing and physical exterior encoder. -/
theorem value_for (hw : 0<a.w)
    (padding : ∀ f (h : a.Returns), a.Reached f h → Nonempty (a.PaddingReads interval dir h))
    (passing : ∀ f (h : a.Returns), a.Reached f h → FieldSiteDirectory.pinsPass L (V.owners R) (V.withPrivate R raw f).1 →
      ∀ u, Nonempty (a.TeamPreparation h bank (prepareTasksFor codec) f u)) :
    letI := Fintype.ofEquiv _ (V.publicFiberEquiv R raw)
    (∏ u, boundedWeight (a.pub u) lib ret fuel (.seq (openCells a.table) (.seq (prepareTasksFor codec) privateReturns))
      (a.regs u) (a.original u) (a.ticks u) a.burst a.clock)=∑ z : V.PublicFiber R raw, V.publicValue R bank z.val :=
  a.value_stage interval dir physical widths bank (prepareTasksFor codec) hw padding passing

end FiniteDiagonal.FieldRawLayout.SignedRouteReceipt

end BorderVNP
end Computability
end OAI
