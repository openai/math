import OAI.Computability.BorderVNP.RoutingISACubeArena
import OAI.Computability.BorderVNP.DiagonalJointWords
import Mathlib.Data.Nat.Choose.Bounds

/-! # Word width for the length-only cube and routing allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Tally Filter

variable {ι : Type*} {scale : ι → ℕ}

/-- A single exponent bounds the scalar on every length in the specified family. -/
def Poly (scale f : ι → ℕ) := ∃ e : ℕ, ∀ i, f i ≤ (scale i+2)^e

/-- Domination preserves a uniform polynomial bound. -/
theorem Poly.mono {f g : ι → ℕ} (h : Poly scale g) (hg : ∀ i, f i ≤ g i) : Poly scale f := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,fun i ↦ (hg i).trans (he i)⟩

/-- Fixed integers are uniformly representable. -/
theorem Poly.const (k : ℕ) : Poly scale (fun _ ↦ k) :=
  ⟨k,fun i ↦ (Nat.lt_two_pow_self (n:=k)).le.trans (Nat.pow_le_pow_left (by omega) _)⟩

/-- Adding two address spans gives another uniformly polynomial span. -/
theorem Poly.add {f g : ι → ℕ} (hf : Poly scale f) (hg : Poly scale g) : Poly scale (fun i ↦ f i+g i) := by
  obtain ⟨e,he⟩ := hf
  obtain ⟨d,hd⟩ := hg
  refine ⟨max e d+1,fun i ↦ ?_⟩
  let B := scale i+2
  have bp : 0 < B := by dsimp [B]; omega
  have a : f i ≤ B^(max e d) := (he i).trans (Nat.pow_le_pow_right bp (le_max_left _ _))
  have b : g i ≤ B^(max e d) := (hd i).trans (Nat.pow_le_pow_right bp (le_max_right _ _))
  change _ ≤ B^(max e d+1)
  rw [pow_succ]
  calc _ ≤ B^(max e d)+B^(max e d) := Nat.add_le_add a b
       _ = B^(max e d)*2 := by omega
       _ ≤ _ := Nat.mul_le_mul_left _ (by dsimp [B]; omega)

/-- Array grids and fixed-width strides preserve uniform polynomial growth. -/
theorem Poly.mul {f g : ι → ℕ} (hf : Poly scale f) (hg : Poly scale g) : Poly scale (fun i ↦ f i*g i) := by
  obtain ⟨e,he⟩ := hf
  obtain ⟨d,hd⟩ := hg
  exact ⟨e+d,fun i ↦ (Nat.mul_le_mul (he i) (hd i)).trans_eq (pow_add ..).symm⟩

/-- The cube dimension is fixed before the length threshold. -/
theorem Poly.pow {f : ι → ℕ} (hf : Poly scale f) (k : ℕ) : Poly scale (fun i ↦ (f i)^k) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e*k,fun i ↦ (Nat.pow_le_pow_left (he i) k).trans_eq (pow_mul ..).symm⟩

/-- Scalar bounds on the public input sizes. The packet, singleton, pair-view,
owner, address, and receiving-cell allocations are computed from these. -/
structure LengthBounds (scale : ι → ℕ) (H : ι → CubeHeaderInstall.Inputs)
    (cells cables maxRows teams stride : ι → ℕ) : Prop where
  /-- High-water address of the preceding geometry computation. -/
  address : Poly scale (fun i ↦ (H i).header)
  /-- Coordinate alphabet size. -/
  symbols : Poly scale (fun i ↦ (H i).d)
  /-- Number of coordinate rows. -/
  axes : Poly scale (fun i ↦ (H i).a)
  /-- Padded block count. -/
  blocks : Poly scale (fun i ↦ (H i).blocks)
  /-- Maximum declared row word. -/
  cap : Poly scale (fun i ↦ (H i).cap)
  /-- Allocated final cell rows. -/
  cellCount : Poly scale cells
  /-- Public geometric cable capacity. -/
  cableCount : Poly scale cables
  /-- Capacity of the native transmission directory. -/
  rowCount : Poly scale maxRows
  /-- Number of teams. -/
  teamCount : Poly scale teams
  /-- Length-only upper bound on one receiving-cell address range. -/
  cellWidth : Poly scale stride

/-- Every one of the native arrays fits a single polynomial in the original
input and batch sizes, with exponent independent of the individual lengths. -/
theorem LengthBounds.arena (H : ι → CubeHeaderInstall.Inputs) (cells cables maxRows teams stride : ι → ℕ)
    (hbound : LengthBounds scale H cells cables maxRows teams stride) (n b h K s : ℕ) :
    Poly scale (fun i ↦ (⟨H i,n,b,h,K,s,cells i,cables i,maxRows i,teams i,stride i⟩ : Layout).stop) := by
  have choose : Poly scale (fun i ↦ (H i).d.choose 2) := (hbound.symbols.pow 2).mono (fun i ↦ Nat.choose_le_pow _ _)
  dsimp only [Layout.stop,Layout.cellBank,Layout.pairBase,TableLayout.reserveEnd,Layout.records,
    Layout.hostDirectory,Layout.pairDirectory,Layout.ownerBase,Layout.teamTotals,Layout.groupWeights,
    Layout.powerBase,Layout.ordinalBase,Layout.widthBase,Layout.dataMean,Layout.cableMean,Layout.demands,
    Layout.nodes,Layout.heads,Layout.publicBase,Layout.vertexBase,Layout.singleBank,Layout.packetEnd,
    CubeHeaderInstall.bankStop,CubeHeaderInstall.Inputs.packetBase,CubeHeaderInstall.Inputs.entries,
    Layout.vertexCap,Layout.alphabet,Physical.Owned.packetTrials,Layout.pairStride,CubeHeaderInstall.Inputs.volume]
  repeat' first
    | exact hbound.address | exact hbound.symbols | exact hbound.axes | exact hbound.blocks
    | exact hbound.cap | exact hbound.cellCount | exact hbound.cableCount | exact hbound.rowCount
    | exact hbound.teamCount | exact hbound.cellWidth | exact choose | exact Poly.const _
    | apply Poly.add | apply Poly.mul | apply Poly.pow

/-- A polynomially sized joint arena fits the paper's chosen logarithmic
hardware word, uniformly over all positive batch lengths. -/
theorem eventually_arena_word {L : ℕ × ℕ → Layout} (E : ℕ)
    (poly : Poly (fun p : ℕ × ℕ ↦ p.2*p.1) (fun p ↦ (L p).stop)) :
    ∀ᶠ t : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (L (t,r)).stop < 2^((TeamScales.logWidth r t)^(E+2)) := by
  obtain ⟨e,he⟩ := poly
  filter_upwards [Diagonal.eventually_polynomial_words (2^e) e E] with t word
  intro r hr
  have addr : (L (t,r)).stop ≤ (r*t+2)^e := he (t,r)
  have span : r*t+2 ≤ 2*(r*t+1) := by omega
  have bound := Nat.pow_le_pow_left span e
  rw [mul_pow] at bound
  exact (addr.trans bound).trans_lt (word r hr)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
