import OAI.Computability.BorderVNP.PackedSewnRecordCompile
import OAI.Computability.BorderVNP.PackedSewnFragmentOwnerBounds
import OAI.Computability.BorderVNP.FiniteSewnFieldDirectory

/-! # Exterior-sewn site directories from physically compiled unordered fragments

Correctness uses the actual physical rows' unique cover of the old incidence
word. The chronological order, maximal ranges, looked-up site prefixes and
numeric equality or clamp records are then all determined by the compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField Crossing ParseBatchSort VPVNP.VerifierNetwork Diagonal.ExternalSew FiniteDiagonal
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6500

variable {σ V : Type*} [Fintype σ] {s n w : ℕ}
    (code : Fin s ↪ Fin (2^w)) (raw : Frame σ (Fragment.Pin n w)) (col : Amounts s w → σ)
    (x : σ → Bool) (site : V ↪ Fin s) (prior : V → Site) (size : V → ℕ)
    (source : ∀ v : V, Fin (prior v).incoming → Option (Fin (size v)))
local notation "key" => (site.trans code).trans Fin.valEmbedding
local notation "xs" => Fragment.list (raw.eval x)

variable (owned : ∀ a ∈ (Fragment.list (raw.eval x)), ∃ v : V, a.site = (code (site v)).val)
    (cover : ∀ v : V, SewnField.Covers (Fragment.siteRuns ((code (site v)).val) (Fragment.list (raw.eval x))) (source v))
    (unique : ∀ v : V, Fragment.UniqueCover (prior v).incoming (Fragment.siteRuns ((code (site v)).val) (Fragment.list (raw.eval x))))
    (widths : ∀ (v : V) (b : Bool), value (fun j => x (col (site v,b,j))) = if b then (prior v).size else (prior v).work)
    (fit : ∀ v : V, (prior v).size + size v < 2^w) (one : 1 < 2^w)

include owned cover unique widths fit one in
/-- Every emitted byte and relocation tag agrees with the true site's canonical
sewing intervals, although the authentic input may list pieces in any order. -/
theorem tape_section : (schema n w).Section ((tape code raw col).eval x) key
    (fun v => (intervals (source v)).map (SewnField.Interval.record (prior v))) := by
  let g := sourceFrame code raw col
  let y := g.eval x
  let old := fun v => (prior v).incoming
  have oldRoom (v) : old v < 2^w := by
    have h := fit v
    change (prior v).work+old v+size v < 2^w at h
    omega
  have newRoom (v) : size v < 2^w := (Nat.le_add_left _ _).trans_lt (fit v)
  have rawFit := Fragment.raw_fits key old size source owned cover oldRoom newRoom
  have merged := source_fragment code raw col x
  have ev : (tape code raw col).eval x = (frame n w).eval y := funext fun z => Frame.subst_eval _ _ _ z
  rw [ev]
  apply frame_section y key prior size source _ _ _ fit one
  · intro i live
    change Fragment.active ((sourceFrame code raw col).eval x ∘ Sum.inl) i = true at live
    rw [merged] at live
    change ∃ v, (Fragment.parse ((sourceFrame code raw col).eval x ∘ Sum.inl) i).site = key v
    rw [merged]
    exact (Fragment.maximal_active_owner_fits key old size source (raw.eval x) owned cover oldRoom newRoom i live).1
  · intro v
    change Fragment.siteRuns (key v) (Fragment.list ((sourceFrame code raw col).eval x ∘ Sum.inl)) = _
    rw [merged]
    exact Fragment.maximal_siteRuns_of_cover _ (fun a ha _ => rawFit a ha) (key v) (source v) (cover v) (unique v)
  · intro i v owner b
    change (Fragment.parse ((sourceFrame code raw col).eval x ∘ Sum.inl) i).site = key v at owner
    rw [merged] at owner
    exact (source_base code raw col x i (site v) b owner).trans (widths v b)

variable {R B : Type*} [Fintype R] [Fintype B] (S : Schema R B) (hist : Frame σ (Pins R B w))

/-- Preserve the entire accumulated selected history and append the real sewing operands. -/
noncomputable def complete := appendFrame hist (tape code raw col)

include owned cover unique widths fit one in
/-- The jointly emitted public image agrees with the actual staged private programs. -/
theorem complete_image (before : S.Image (hist.eval x) key prior) :
    (S.append (schema n w)).Image ((complete code raw col hist).eval x) key
      (fun v => stage (prior v) (size v) (intervals (source v))) := by
  have added := tape_section code raw col x site prior size source owned cover unique widths fit one
  have full := appendFrame_section S (schema n w) hist (tape code raw col) x key _ _ (before.toSection S) added
  exact full.image _ _ (fun v => (stage_rows ..).symm)

/-- The predecessor is computed once and its immutable fields are wired directly to the append. -/
theorem complete_size : (complete code raw col hist).size = hist.size + (tape code raw col).size :=
  appendFrame_size _ _

private theorem cast_cover {a b next : ℕ} (h : a=b) (read : Fin b → Option (Fin next)) (runs : List SewnField.Interval)
    (cov : SewnField.Covers runs read) : SewnField.Covers runs (fun k : Fin a => read (Fin.cast h k)) := by subst b; exact cov

private theorem cast_unique {a b : ℕ} (h : a=b) (runs : List SewnField.Interval)
    (u : Fragment.UniqueCover b runs) : Fragment.UniqueCover a runs := h.symm ▸ u

section Directory
variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {oldWidth : A → ℕ} (N : Network D A oldWidth) (lane : P ↪ Σ a, Fin (oldWidth a))
    {cw : Cable → ℕ} (bundle : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = bundle.layout.attach f)
    {ne np : ℕ} (edge : (N.Edge ⊕ Cable) ↪ Fin ne) (port : U ↪ Fin np)
    {K : Type*} [Field K] {T : N.Tables K} (dir : FieldSiteDirectory N T) (loc : ∀ v, (dir.site v).Local)
    (names : N.Site ↪ Fin s)

local notation "sewn" => Network.packExternal bundle.layout gw owner
local notation "realKey" => (names.trans code).trans Fin.valEmbedding
local notation "readLane" => sewnRead N lane bundle gw freeLane owner aligned dir.edgeID dir.portID edge port
local notation "finalDir" => sewnDirectory N lane bundle gw freeLane owner aligned edge port dir loc

/-- The actual finite or signed field directory at the sewn terminal has the physically
emitted immutable row image, with the exact predecessor and successor incidence orderings. -/
theorem directory_image (before : S.Image (hist.eval x) realKey dir.site)
    (owns : ∀ a ∈ xs, ∃ v : N.Site, a.site=realKey v)
    (covers : ∀ v : N.Site, SewnField.Covers (Fragment.siteRuns (realKey v) xs) (readLane v))
    (once : ∀ v : N.Site, Fragment.UniqueCover (incoming N v) (Fragment.siteRuns (realKey v) xs))
    (reads : ∀ v b, value (fun j => x (col (names v,b,j))) = if b then (dir.site v).size else (dir.site v).work)
    (fits : ∀ v, (dir.site v).size + incoming sewn v < 2^w) (one : 1 < 2^w) :
    (S.append (schema n w)).Image ((complete code raw col hist).eval x) realKey (finalDir).site :=
  complete_image code raw col x names dir.site (incoming sewn)
    (programRead N lane bundle gw freeLane owner aligned edge port dir) owns
    (fun v => cast_cover (dir.incoming v) (readLane v) _ (covers v))
    (fun v => cast_unique (dir.incoming v) _ (once v)) reads fits one S hist before

end Directory

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
