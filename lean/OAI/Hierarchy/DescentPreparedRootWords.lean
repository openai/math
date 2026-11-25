import OAI.Hierarchy.DescentPreparedRootInputs

namespace OAI
/-! # Complete packed output words from the original prepared private root books -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentSixParty.Chronology DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace RootTable
variable {N H G M w : ℕ} (t : RootTable N)
local notation "rows" => H*chunks G M

theorem evaluated_words (base mid out : ℕ) (input : Bank) (sourceAt : input.base=mid)
    (sourceBits : input.bits=Nat.clog 2 rows) (written : t.stop base H G M ≤ mid)
    (prior : ∀j,(t.reads j).Fits w mid) (positioned : mid+RootArena.span rows ≤ out) (complete : out+rows < 2^w)
    (packed : M*max (t.field*N) t.outputBits ≤ w/2) (pos : 0 < M) (mem : Memory w)
    (actual : (t.literals base H G M w).Resident mem) (value : Fin H→Fin G→Fin N→Cell t.field)
    (source : ∀i,Source (t.reads i) (fun v g=>value v g i) M mem) :
    let menu:=t.terms base H G M input
    let emitter:=assembly menu.tables t.reads
    let dst:=imageBank H G M out menu.menu (image mid rows emitter mem)
    ∀p : Row H G M,dst (out+(row H G M p).val)=
      ((data (fun v g=>t.law (encode t.field N (value v g))) p).val:Word w) := by
  obtain ⟨bounds,fit,dict,mask⟩:=t.geometry_at base mid out input sourceAt sourceBits written prior positioned complete packed
  have small : t.stop base H G M < 2^w := by omega
  obtain ⟨gates,lut⟩:=t.resident_at base input mem small actual
  let p:=t.terms base H G M input
  let emit:=t.law ∘ (encode t.field N)
  have identify : (emit ∘ (encode t.field N).symm)=t.law := by funext z;simp [emit]
  have room : mid+rows < 2^w := by have:=RootArena.le_span rows;omega
  exact (DescentIssuedGoodHeaders.gathered_words emit p.tables t.reads p.menu mid out value pos mem
    bounds gates source room fit (identify.symm ▸ lut) dict mask sourceAt).2.1
end RootTable

namespace Receiver
open DescentSharedBookScan
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "J" => 2^c
local notation "slots" => H*chunks J M
local notation "A" => RootTemplates.arena (a.headerEnd b) H J M r n D
variable (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n))
local notation "rid" => (rootIndex r (2^n) p).val
local notation "start" => b.atPage a.projectionEnd H J M p
local notation "input" => b.target a.projectionEnd H J M p
local notation "tbl" => (b.table p).2

theorem prepared_root_words (value : Fin H→Fin J→Fin (b.table p).1→Cell (tbl).field)
    (prior : ∀i,((tbl).reads i).Fits w ((A).middle rid))
    (packed : M*max ((tbl).field*(b.table p).1) (tbl).outputBits ≤ w/2)
    (source : ∀i,Source ((tbl).reads i) (fun v g=>value v g i) M (a.rootInputState b space m p))
    (positive : 0 < M) :
    Reads ⟨(A).output rid,Nat.clog 2 slots⟩
      (fun h g=>(tbl).law (encode (tbl).field (b.table p).1 (value h g))) M (a.preparedImage b space m) := by
  intro row_
  have name:=(rootIndex r (2^n) p).isLt
  have head:=b.bounds a.projectionEnd H J M w p
  have below : (tbl).stop start H J M ≤ a.headerEnd b :=
    head.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  have mid : a.headerEnd b ≤ (A).middle rid := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have lo : (A).middle rid ≤ (A).output rid := Nat.le_add_right ..
  change a.preparedImage b space m ((A).output rid+(row H J M row_).val)=_
  rw [a.gatheredImage b space m p _ (lo.trans (Nat.le_add_right ..))
    (Nat.add_lt_add_left (row H J M row_).isLt _)]
  exact (tbl).evaluated_words start _ _ input rfl rfl (below.trans mid) prior le_rfl (space.rows p).2
    packed positive _ (a.rootInput_tables b space m p) value source row_

end Receiver
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
