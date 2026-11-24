import OAI.Computability.VPVNP.CompressorShrinkResidentPackets
import OAI.Computability.VPVNP.CompressorResidentPacketScans
import OAI.Computability.VPVNP.CompressorShrinkResidentFootprint

/-! # Chronological native source walk of the resident directories -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner PhaseRecipe SourceTransport SourceOnline
open ShrinkResidentRun ShrinkResidentLayout
open scoped Fin.CommRing

variable {w : ℕ}

/-- Addresses the resident group may write, comprising its allocated array interval and header
offsets 30 through 35. -/
def Mutable (D : Values w) (x : ℕ) : Prop :=
  (D.layout.first ≤ x ∧ x < D.layout.endAddr) ∨ (D.level+30 ≤ x ∧ x < D.level+36)

/-- The chosen resident stage runs from cursor zero, reaches its limit, reads above the lower
bound, and writes only within its mutable region. -/
structure Native (P : Plan) (D : Values w) (low : ℕ) (j : Stage) (m : Memory w) (rs : List (Report w)) : Prop where
  run : let M := ((j.visit P).worker.table.instantiate w (j.bank P D)).program
    runSegment M j.fuel (some 0) m (List.replicate (j.limit D) []) = some rs
  progress : Progress (j.limit D : Word w) 0 rs
  read : Reads (low ≤ ·) (eventLog rs)
  write : Writes (Mutable D) (eventLog rs)

variable (P : Plan) {g : ℕ} (X : State P.exponent (packingLaneBits P.exponent g))
variable (first level : ℕ) (absolute role : Word w) (side : Bool)

/-- Assemble the resident-stage operands from the state layout, level header, absolute and role
array heads, and selected side. -/
def values : Values w := ⟨layout X first,level,absolute,role,side⟩

local notation "D" => values P X first level absolute role side

theorem scan_walk (maps : Bool) {m : Memory w} {r : Passes w}
    (built : Built X first absolute role side maps m r)
    (space : Areas X first absolute role) (dir : ShrinkResidentDirectory.Absolute X absolute m)
    (low : ℕ) (dataStart : low ≤ first) (absStart : low ≤ absolute.val) (roleStart : low ≤ role.val) :
    SourceWalk (Native P D low) (scans maps) m r.all := by
  let L := layout X first
  let p := ownerBank X first absolute role side maps
  obtain ⟨shape,rd,wr⟩ := built.owners.scanned X maps p rfl (space.owner side maps) dir
  obtain ⟨_,h0,h1,_,_,_,_⟩ := frame X first maps space.fit
  change (p 3).val = L.owner maps at h1
  have nfit : L.size maps < 2^w := h0 ▸ ((layout X first).params P.exponent maps w 0).isLt
  obtain ⟨owner,counts,rows,last⟩ := L.ranges maps
  change first ≤ L.owner maps at owner
  have owners : Native P D low (.owners maps) m r.owners := by
    refine ⟨built.owners.native,shape.toProgress nfit,?_,?_⟩
    · intro a v ha
      rcases rd a v ha with h|h
      · exact absStart.trans h.1
      · exact roleStart.trans h.1
    · intro a v ha
      have h := wr a v ha
      change (p 3).val ≤ a.val ∧ a.val < (p 3).val+L.size maps at h
      rw [h1] at h
      exact .inl ⟨owner.trans h.1,by change a.val < L.endAddr; omega⟩
  obtain ⟨cp,cr,cw⟩ := counter_scan X first absolute role side maps built space.fit
  have clear : Native P D low (.clear maps) (r.mid m) r.clear := by
    refine ⟨built.clear,cp,fun a v hv => False.elim (cr a v hv),?_⟩
    intro a v hv
    have ha := cw a v hv
    change L.counts maps ≤ a.val ∧ a.val < L.rows maps at ha
    exact .inl ⟨by change first ≤ a.val; omega,by change a.val < L.endAddr; omega⟩
  obtain ⟨ap,ar,aw⟩ := preimage_scan X first absolute role side maps built space.fit
  have append : Native P D low (.append maps) (r.cleared m) r.collect :=
    ⟨built.collect,ap,fun a v h => dataStart.trans (ar a v h).1,fun a v h => .inl (aw a v h)⟩
  have path := SourceWalk.next owners (SourceWalk.next clear (SourceWalk.singleton append))
  simpa only [scans,Passes.all,List.append_assoc] using path

theorem publish_walk (low : ℕ) (fit : level+36 ≤ 2^w) (m : Memory w) :
    SourceWalk (Native P D low) ((List.finRange 6).map Stage.header) m
      (List.ofFn (ShrinkResidentsPlan.headerReport level (layout X first) w)) := by
  let L := layout X first
  have go (is : List (Fin 6)) (mem : Memory w) :
      SourceWalk (Native P D low) (is.map Stage.header) mem (is.map (ShrinkResidentsPlan.headerReport level L w)) := by
    induction is generalizing mem with
    | nil => exact .done _
    | cons i is ih =>
      have shape := header_scan (w := w) level L i fit
      refine SourceWalk.next (rs := [ShrinkResidentsPlan.headerReport level L w i]) ?_ (ih _)
      refine ⟨ShrinkResidentsPlan.header_source P.chosen P.first P.oldLevel level L i mem,shape.1,
        fun a v ha => False.elim (shape.2.1 a v ha),?_⟩
      intro a v ha
      have h := shape.2.2 a v ha
      change (first ≤ a.val ∧ a.val < L.endAddr) ∨ (level+30 ≤ a.val ∧ a.val < level+36)
      exact .inr (by have := i.isLt; omega)
  simpa only [List.ofFn_eq_map] using go (List.finRange 6) m

/-- Both tables and the six headers execute against the post-memory of the
preceding stage. All modified cells lie in the declared two intervals. -/
theorem native_walk (space : Areas X first absolute role) (m : Memory w)
    (dir : ShrinkResidentDirectory.Absolute X absolute m) (roles : DemandRAM.RoleColumns X side role.val m)
    (low : ℕ) (dataStart : low ≤ first) (absStart : low ≤ absolute.val) (roleStart : low ≤ role.val)
    (hdrFit : level+36 ≤ 2^w) :
    ∃ h r : Passes w, Built X first absolute role side false m h ∧
      Built X first absolute role side true (h.final m) r ∧
      SourceWalk (Native P D low) order m
        ((h.all++r.all)++List.ofFn (ShrinkResidentsPlan.headerReport level (layout X first) w)) := by
  obtain ⟨h,r,hh,hr,_,_⟩ := both X first absolute role side space m dir roles
  have dir' := (hh.inputs X first absolute role side false dir roles space).1
  have hw := scan_walk P X first level absolute role side false hh space dir low dataStart absStart roleStart
  have rw := scan_walk P X first level absolute role side true hr space dir' low dataStart absStart roleStart
  rw [← h.after_all m] at rw
  exact ⟨h,r,hh,hr,(hw.append rw).append (publish_walk P X first level absolute role side low hdrFit _)⟩

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
