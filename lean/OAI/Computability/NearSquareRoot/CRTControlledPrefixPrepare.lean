import OAI.Computability.NearSquareRoot.CRTControlledLift
import OAI.Computability.NearSquareRoot.NamedPackedRate

/-! # One physical row-preparation command at all prefix geometries -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PrefixCommand

open IntegerMultiplication Code Strip Loom Adic

/-- The semantic index supplies arbitrary tree records. Only the two unary
lengths, the shared header, and the original ordered array are on the tape. -/
structure World (H : Type) where
  p : ℕ
  n : ℕ
  w : ℕ
  shared : H
  cell : Block 2 p × Block 2 n → Tree
  cellBound : ∀ z, (cell z).count ≤ 2*w+1

def descriptor {H : Type} (z : World H) := ((tally z.p,tally z.n),z.shared)

def regime (H : Type) [Codec H] : Regime (World H) := ⟨size ∘ descriptor,send ∘ descriptor,Dom.base _⟩

def count {H : Type} (z : World H) := ((line 2 z.p).cart (line 2 z.n)).count

def input {H : Type} [Codec H] (z : World H) :=
  Tree.fork (send (descriptor z)) (stripe ((line 2 z.p).cart (line 2 z.n)) z.cell)

def output {H : Type} [Codec H] (z : World H) :=
  stripe (line 2 z.p) (fun a => Tree.fork (send z.shared) (stripe (line 2 z.n) (fun b => z.cell (a,b))))

private theorem prepare_rip (H : Type) [Codec H] :
    Rip (regime H) count World.w input output := by
  let s (z : World H) := line 2 z.p
  let t (z : World H) := line 2 z.n
  have hdr : (regime H).Has descriptor := Regime.self
  have hs := Adic.terminal (p := 2) (by decide) (World.p (H := H)) (hdr.ez (Easy.fst.compose Easy.fst))
  have ht := Adic.terminal (p := 2) (by decide) (World.n (H := H)) (hdr.ez (Easy.fst.compose Easy.snd))
  have hv : Manifest _ (World.w (H := H)) World.cell :=
    ⟨2,fun z i => (z.cellBound i).trans (by omega)⟩
  have live := hv.lives (hs.product ht)
  have ns (z : World H) : (s z).count ≤ count z := by
    unfold count; rw [Series.count_cart]; exact Nat.le_mul_of_pos_right _ (ht.1 z)
  have nt (z : World H) : (t z).count ≤ count z := by
    unfold count; rw [Series.count_cart]; exact Nat.le_mul_of_pos_left _ (hs.1 z)
  have pn z := (hs.1 z).trans (ns z)
  have data := Drive.self pn live
  have header := Drive.fetch pn live
  have rules := (header.chain (hs.supply ns)).twice (header.chain (ht.supply nt))
  have rows := Rip.carve s t World.cell rules data hs.1 ht.1 (fun z => (Series.count_cart (s z) (t z)).symm.le)
  exact Rip.coalesce (fun z _ => send z.shared) (fun z a => stripe (t z) (fun b => z.cell (a,b)))
    (header.chain (clones hs ns (send ∘ World.shared) (hdr.ez Easy.snd))) rows

noncomputable def degree (H : Type) [Codec H] := (prepare_rip H).choose

private theorem emitted (H : Type) [Codec H] : ∃ c, NamedPacked.CarriesAt c
    (mass (regime H) count World.w (degree H)) input output :=
  NamedPacked.CarriesAt.exists_of_carries (prepare_rip H).choose_spec

noncomputable def prepare (H : Type) [Codec H] : Cmd := (emitted H).choose

theorem preparedAt (H : Type) [Codec H] : NamedPacked.CarriesAt (prepare H)
    (mass (regime H) count World.w (degree H)) input output := (emitted H).choose_spec

theorem prepared (H : Type) [Codec H] : EffectiveTask.Runs (prepare H)
    (fun z : World H => ⌈mass (regime H) count World.w (degree H) z⌉₊) input output :=
  (preparedAt H).release

end Controlled.PrefixCommand

end NearSquareRoot
end Computability
end OAI
