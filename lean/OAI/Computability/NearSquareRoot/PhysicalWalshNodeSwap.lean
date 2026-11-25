import OAI.Computability.NearSquareRoot.PhysicalWalshSwapOrdinal
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader

/-! # Interchanging two wide slots of a recursive Walsh node

A rectangular command sees only the three unary field widths. The suffix,
including the reserved low bits of the last moving field, travels with every
record. Both runtime and peak space charge this payload at its actual size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap

open IntegerMultiplication Code Strip Strip.Dims Loom Adic NearSquareRoot.InterchangePayload
open NearSquareRoot.Space

structure Geometry where
  pre : ℕ
  gap : ℕ
  wing : ℕ

namespace Geometry

def header (z : Geometry) := (tally z.pre, tally z.gap, tally z.wing)

def grid (z : Geometry) := stock 2 (field 2 z.pre) (field 2 z.gap) [] z.wing

abbrev Key (z : Geometry) := SpanKey (field 2 z.pre) (field 2 z.gap) [] (Block 2 z.wing)

end Geometry

/-- An instance contains its physical bitstring at each rectangular address. -/
structure Packet where
  geometry : Geometry
  width : ℕ
  bits : ℕ → List Bool
  exactWidth : ∀ x, (bits x).length = width

namespace Packet

def input (t : Packet) := send (t.geometry.header, (List.range t.geometry.grid.count).map t.bits)

def output (t : Packet) := send ((List.range t.geometry.grid.count).map (t.bits ∘ SwapOrdinal.source (2^t.geometry.wing) (room (field 2 t.geometry.gap)) 1))

def volume (t : Packet) := t.geometry.grid.count * t.width

end Packet

/-- Extract one header degree for the uniform rectangular machine, before
choosing the low-bit reserve. Every family of packets reaching that reserve
runs in the bit volume times the near-root rate of the moving field. -/
theorem packed {ρ : ℝ} (rate : 1/2 < ρ) : ∃ D : ℕ, ∀ {I : Type} (data : I → Packet),
    (∀ i, (size (data i).geometry.header + 1)^D ≤ (data i).width) →
    BoundedTask (fun i => ⌈((data i).volume : ℝ) * (((data i).geometry.wing+1 : ℕ):ℝ)^ρ⌉₊)
      (Packet.volume ∘ data) (Packet.input ∘ data) (Packet.output ∘ data) := by
  let X := Packet × ℕ
  let z (x : X) := x.1.geometry
  let r : Regime X := ⟨fun x => size (z x).header, fun x => send (z x).header, Dom.base _⟩
  let cap (x : X) := max x.1.width x.2
  have hd : r.Has (fun x => (z x).header) := r.self
  have hp : r.Has (fun x => tally (z x).pre) := hd.ez Easy.fst
  have hg : r.Has (fun x => tally (z x).gap) := hd.ez (Easy.snd.compose Easy.fst)
  have hn : r.Has (fun x => tally (z x).wing) := hd.ez (Easy.snd.compose Easy.snd)
  let P (x : X) := field 2 (z x).pre
  let G (x : X) := field 2 (z x).gap
  let B (_ : X) : Tape := []
  let n (x : X) := (z x).wing
  have guard (x : X) (d : ℕ) (hd : d ∈ P x ++ G x ++ B x) : d ≤ Net.Shuttle.base := by
    simp only [B,List.append_nil,List.mem_append] at hd
    rcases hd with h|h <;> exact ((ivory (p:=2) (by decide) d h).2).trans Net.Shuttle.base_large.le
  have cmd := SwapOrdinal.bounded_range rate P G B n
    hn (Told.carrier (q:=2) (by decide) _ hp) (Told.carrier (q:=2) (by decide) _ hg) Told.nil guard
    cap (fun x => x.1.width) (fun _ => le_max_left ..) (fun x => x.1.bits) (fun x j _ => x.1.exactWidth j)
  let select (K : ℕ) (x : Packet) : X := (x,(size x.geometry.header+1)^K)
  obtain ⟨D,run⟩ := cmd.select_payload select (fun _ _ => le_max_right ..)
  refine ⟨D,fun {I} data room => ?_⟩
  have bound (i : I) : cap (select D (data i)) = (data i).width := max_eq_left (room i)
  have h := run.on data
  change BoundedTask (fun i => ⌈((data i).geometry.grid.count:ℝ)*(cap (select D (data i)) : ℝ) *
      (((data i).geometry.wing+1 : ℕ):ℝ)^ρ⌉₊)
    (fun i => (data i).geometry.grid.count * cap (select D (data i)))
    (Packet.input ∘ data) (Packet.output ∘ data) at h
  simp only [bound] at h
  simpa only [Packet.volume,Nat.cast_mul,Function.comp_def] using h

end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
