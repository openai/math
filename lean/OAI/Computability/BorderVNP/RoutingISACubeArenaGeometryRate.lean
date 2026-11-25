import OAI.Computability.BorderVNP.RoutingISACubeArenaRate

/-! # Polynomial word bounds for the actual cube header following geometry

The source scalars determine the secondary address and the declaration cap.
Bounding these derived quantities uses the geometry allocation and the actual
partition of padded bits into full packet incidences and singleton slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Physical CubeHeaderInstall

variable {ι : Type*} {scale : ι → ℕ}

/-- Both summands of the declaration cap are bounded by the ordered product
label pairs and their public padding widths. -/
theorem declarationCap_le (n d blocks b h s : ℕ) :
    declarationCap n d blocks b h s ≤
      (blocks*(d^(n+1))^2)*(h*s)+(d^(n+1))^2*(blocks*(h*b)) := by
  have packets := packet_count n d blocks 1
  simp only [padded,Nat.mul_one] at packets
  have packetBound := (Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 2) n)).trans packets
  have slots := Fintype.card_congr (splitSlot n d blocks (h*b))
  rw [Fintype.card_sum] at slots
  have singles : Fintype.card (SingleSlot n d blocks (h*b)) ≤ (d^(n+1))^2*(blocks*(h*b)) := calc
    _ ≤ Fintype.card (Slot n d blocks (h*b)) := (Nat.le_add_left _ _).trans_eq slots.symm
    _ = _ := by simp [Slot,Label,pow_two]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ packetBound) singles

/-- With the template fixed, the complete declaration cap grows polynomially
in the alphabet and the number of padded blocks. -/
theorem declarationCap_poly {d blocks : ι → ℕ} (n b h s : ℕ)
    (symbols : Poly scale d) (padding : Poly scale blocks) :
    Poly scale (fun i => declarationCap n (d i) (blocks i) b h s) := by
  have z := (symbols.pow (n+1)).pow 2
  exact (((padding.mul z).mul (Poly.const (h*s))).add
    (z.mul (padding.mul (Poly.const (h*b))))).mono (fun _ => declarationCap_le ..)

/-- The native arena size for the header actually installed at the geometry
sentinel is bounded by polynomials in the public length parameters. -/
theorem geometryArena_poly (n b h K s : ℕ)
    (fresh profile gates outputs width word d blocks cells cables rows teams stride : ι → ℕ)
    (hf : Poly scale fresh) (hp : Poly scale profile) (hg : Poly scale gates)
    (ho : Poly scale outputs) (hw : Poly scale width) (hword : Poly scale word)
    (hd : Poly scale d) (hb : Poly scale blocks) (hc : Poly scale cells)
    (hwire : Poly scale cables) (hr : Poly scale rows) (ht : Poly scale teams)
    (hs : Poly scale stride) :
    Poly scale (fun i =>
      (⟨geometryInputs (fresh i) (profile i) (gates i) (outputs i) (width i) (word i)
          (d i) n (blocks i) b h s,n,b,h,K,s,cells i,cables i,rows i,teams i,stride i⟩ : Layout).stop) := by
  apply LengthBounds.arena
  refine ⟨?_,hd,Poly.const (n+1),hb,declarationCap_poly n b h s hd hb,hc,hwire,hr,ht,hs⟩
  have base := ((Poly.const 8).add ((Poly.const 4).mul hg)).add ((Poly.const 2).mul hp)
  have output := ho.mul (hw.add (Poly.const 1))
  have workspace := (base.add output).mul (hword.add (Poly.const 2))
  exact (hf.add workspace).mono (fun _ => GeometryAdvice.Allocation.stop_le ..)

/-- The hardware word occurring in the geometry allocation is itself a
polynomially bounded scalar for every fixed logarithmic power. -/
theorem scheduleWord_poly (order batch : ι → ℕ) (E : ℕ) :
    Poly (fun i => batch i*order i) (fun i => (TeamScales.logWidth (batch i) (order i))^E) := by
  apply Poly.pow
  refine ⟨2,fun i => ?_⟩
  change TeamScales.logWidth (batch i) (order i) ≤ (batch i*order i+2)^2
  rw [Shortening.PublicCapacity.public_logWidth]
  have le : Nat.clog 2 (2*order i*batch i) ≤ 2*order i*batch i :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  calc
    _ ≤ 2*order i*batch i := le
    _ = 2*(batch i*order i) := by ring
    _ ≤ (batch i*order i+2)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)

/-- Polynomially bounded words fit the selected logarithmic-power machine
simultaneously for every admissible instance of a sufficiently large length. -/
theorem Poly.eventually_word (order batch value : ι → ℕ) (E : ℕ)
    (space : Poly (fun i => batch i*order i) value) :
    ∃ N : ℕ, ∀ i, N ≤ order i → 1 ≤ batch i →
      value i < 2^((TeamScales.logWidth (batch i) (order i))^(E+2)) := by
  obtain ⟨e,he⟩ := space
  obtain ⟨N,word⟩ := Filter.eventually_atTop.mp (Diagonal.eventually_polynomial_words (2^e) e E)
  refine ⟨N,fun i orderLarge batchPos => ?_⟩
  have bound := Nat.pow_le_pow_left (show batch i*order i+2 ≤ 2*(batch i*order i+1) by omega) e
  rw [mul_pow] at bound
  exact ((he i).trans bound).trans_lt (word _ orderLarge _ batchPos)

/-- A single threshold works for every admissible geometric arena, including
multiple choices of geometry or batch at the same input length. -/
theorem eventually_geometry_word (order batch : ι → ℕ) (L : ι → Layout) (E : ℕ)
    (space : Poly (fun i => batch i*order i) (fun i => (L i).stop)) :
    ∃ N : ℕ, ∀ i, N ≤ order i → 1 ≤ batch i →
      (L i).stop < 2^((TeamScales.logWidth (batch i) (order i))^(E+2)) :=
  space.eventually_word order batch _ E

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
