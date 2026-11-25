import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorPacket
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeConjugate

/-! # Named commands for composable flat Walsh routing passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile
open CommonRegisters GeneratorSyntax Filter

/-- A single named pass consumes the compact node header and one ordered row. -/
def Flat {a W : ℕ} (scan arena : Shape → ℕ) (F : (s : Shape) → Data s → Data s) (c : Cmd) : Prop :=
  ClosedRuns c (fun t : XorInput W => scan t.shape) (fun t => arena t.shape)
    (fun t => send (Header.wire (a+1) t.shape, laneFlat (a+1) W t.shape t.row))
    (fun t => send (laneFlat (a+1) W t.shape (F t.shape t.row)))

private abbrev Source := Header.Wire × List Dusk.Pair
private def retain (z : Source) := (z,z.1)

structure Kit where
  save : Cmd
  swap : Cmd
  erase : Cmd

/-- Keep the descriptor parked during the first pass and prepend it again
before the next call. The accumulator is always one ordered row. -/
def Kit.chain (K : Kit) (c d : Cmd) := (((K.save.join (left c)).join K.swap).join d)

structure Legal (K : Kit) (R : ℕ) : Prop where
  positive : 0 < R
  saveReg : Within R K.save
  swapReg : Within R K.swap
  eraseReg : Within R K.erase
  saves : Scans K.save retain
  swaps : Scans K.swap (Prod.swap : List Dusk.Pair × Header.Wire → Source)
  erases : Scans K.erase (Prod.snd : Source → List Dusk.Pair)

theorem exists_kit : ∃ (K : Kit) (R : ℕ), Legal K R := by
  obtain ⟨c,hc⟩ := exists_scanner (show Easy retain from Easy.identity.pair Easy.fst)
  obtain ⟨d,hd⟩ := exists_scanner (Easy.exchange (X := List Dusk.Pair) (Y := Header.Wire))
  obtain ⟨e,he⟩ := exists_scanner (Easy.snd (X := Header.Wire) (Y := List Dusk.Pair))
  obtain ⟨R,hR,rc,rd,re⟩ := ((eventually_gt_atTop 0).and ((RegisterSelect.within_eventually c).and
    ((RegisterSelect.within_eventually d).and (RegisterSelect.within_eventually e)))).exists
  exact ⟨⟨c,d,e⟩,R,hR,rc,rd,re,hc,hd,he⟩

theorem Kit.effective_chain (K : Kit) {J : Type} [Primcodable J] {c d : J → Cmd}
    (hc : Effective ltr c) (hd : Effective ltr d) : Effective ltr (fun j => K.chain (c j) (d j)) :=
  (((effective_const ltr K.save).join (KernelEffectiveFamily.effective_left hc)).join (effective_const ltr K.swap)).join hd

variable {K : Kit} {R M : ℕ}

theorem Legal.within_erase (hk : Legal K R) (le : R ≤ M) : Within M K.erase :=
  RegisterSelect.within_mono le _ hk.eraseReg

theorem Legal.within_chain (hk : Legal K R) (le : R ≤ M) {c d : Cmd}
    (hc : Within M c) (hd : Within M d) : Within M (K.chain c d) :=
  ⟨⟨⟨RegisterSelect.within_mono le _ hk.saveReg,KernelEffectiveFamily.within_left (hk.positive.trans_le le) hc⟩,
    RegisterSelect.within_mono le _ hk.swapReg⟩,hd⟩

variable {a W : ℕ} {scan arena : Shape → ℕ}
private def meter (cost : ∀ s, arena s ≤ scan s) : Meter Shape := ⟨scan,arena,cost,fun _ _ _ _ => True⟩

private theorem finish {I : Type} {u : I → Shape} {q r : I → Tree} {c : Cmd} {cost : ∀ s, arena s ≤ scan s}
    (h : Runs c (meter cost) 0 u q r) : ClosedRuns c (scan ∘ u) (arena ∘ u) q r := by
  obtain ⟨C,hr⟩ := h
  exact ⟨C,fun i env park b hb => by simpa [meter] using hr i env 0 0 trivial park b hb⟩

private theorem extents (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    (t : XorInput W) : size (Header.wire (a+1) t.shape) ≤ arena t.shape ∧
      ∀ v : Data t.shape, size (laneFlat (a+1) W t.shape v) ≤ arena t.shape := by
  have room := PhysicalWalshContext.fitsLayout (m := meter cost) (coords a W) Shape.w (Header.wire (a+1)) fit
  refine ⟨?_,fun v => ?_⟩
  · have h := room.header t.shape
    change size (PhysicalWalshGrid.header (coords a W) Shape.w t.shape) + size (Header.wire (a+1) t.shape)+1 ≤ arena t.shape at h
    omega
  · have h := room.row t.shape v
    change size (((coords a W).rows t.shape).map (Dusk.mark ∘ v)) ≤ arena t.shape at h
    rw [coords_range a W t.shape t.positive] at h
    exact h

open private Scans.atInput from OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound

/-- A zero-stage route drops the descriptor and returns the original row. -/
theorem Legal.runs_id (hk : Legal K R) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s) :
    Flat (a:=a) (W:=W) scan arena (fun _ x => x) K.erase := by
  let u := @XorInput.shape W
  let q (t : XorInput W) := (Header.wire (a+1) t.shape, laneFlat (a+1) W t.shape t.row)
  apply finish (cost:=cost) (u:=u)
  apply Scans.atInput (m:=meter cost) (u:=u) hk.erases q 3
  intro t
  have ⟨hh,hr⟩ := extents cost fit t
  have := hr t.row
  change size (Header.wire (a+1) t.shape)+size (laneFlat (a+1) W t.shape t.row)+1 ≤ 3*(arena t.shape+1)
  omega

/-- The local clocks add. The same resident row arena serves both calls. -/
theorem Legal.runs_chain (hk : Legal K R) (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    {F G : (s : Shape) → Data s → Data s} {c d : Cmd}
    (first : Flat (a:=a) (W:=W) scan arena F c) (second : Flat (a:=a) (W:=W) scan arena G d) :
    Flat (a:=a) (W:=W) scan arena (fun s x => G s (F s x)) (K.chain c d) := by
  let u := @XorInput.shape W
  let hdr (t : XorInput W) := Header.wire (a+1) t.shape
  let x (t : XorInput W) := laneFlat (a+1) W t.shape t.row
  let y (t : XorInput W) := laneFlat (a+1) W t.shape (F t.shape t.row)
  let z (t : XorInput W) := laneFlat (a+1) W t.shape (G t.shape (F t.shape t.row))
  let next (t : XorInput W) : XorInput W := {t with row := F t.shape t.row}
  let m := meter cost
  have hh (t) : size (hdr t) ≤ arena (u t) := (extents cost fit t).1
  have begin_ := Scans.atInput (m:=m) (u:=u) hk.saves (fun t => (hdr t,x t)) 3 (fun t => by
    have h := (extents cost fit t).2 t.row; have h' := hh t
    change size (x t) ≤ arena (u t) at h
    change size (hdr t)+size (x t)+1 ≤ 3*(arena (u t)+1)
    omega)
  have run1 : Runs c m 0 u (fun t => send (hdr t,x t)) (fun t => send (y t)) := Runs.closed first
  have keep := run1.left (fun t => send (hdr t)) 1 (fun t => by
    change size (hdr t) ≤ 1*(arena (u t)+1); have := hh t; omega)
  have exchange := Scans.atInput (m:=m) (u:=u) hk.swaps (fun t => (y t,hdr t)) 3 (fun t => by
    have h := (extents cost fit t).2 (F t.shape t.row); have h' := hh t
    change size (y t) ≤ arena (u t) at h
    change size (y t)+size (hdr t)+1 ≤ 3*(arena (u t)+1)
    omega)
  have run2 : Runs d m 0 u (fun t => send (hdr t,y t)) (fun t => send (z t)) := Runs.closed (second.on next)
  exact finish (((begin_.seq keep).seq exchange).seq run2)

end PhysicalWalshCompileXorRoute

end NearSquareRoot
end Computability
end OAI
