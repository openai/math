import OAI.Computability.BorderVNP.DiagonalExternalSewVolume
import OAI.Computability.BorderVNP.DiagonalExternalSewBlockAddress

/-! # Physical partner-rank cables in Proposition 7.2

At one initial site of one team, the ordered intervals for the actual
processor and skipped partner rank use at most four public cable records
and at most one block of bit incidences. After the epochs, each exterior
bit contributes at most one unit of intercell width regardless of which
cells received its two ends.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Finset
open scoped Classical


variable {R r : ℕ} (literal stride link g : ℕ)

/-- Positive intervals add at most four public exterior descriptors per site and copy. -/
theorem physical_ends_per_block (fits : R*link ≤ stride) (hg : 0 < g) (small : g ≤ link)
    (u : Fin (R+1)) (s : ℕ) :
    (univ.filter fun x : Bool × Pieces (fieldStart (r := r) literal stride link) g link =>
      fieldBlock literal stride link g x.2 x.1 = (u,s)).card ≤ 4 := by
  exact ends_per_block (ends := physicalEnds R r) (literal := literal) (stride := stride) (link := link) (g := g)
    fits hg small u s

/-- The sum of the widths of all exterior ends at one site fits its real block. -/
theorem physical_width_per_block (fits : R*link ≤ stride) (hg : 0 < g) (u : Fin (R+1)) (s : ℕ) :
    (∑ x : {x : Bool × Pieces (fieldStart (r := r) literal stride link) g link //
      fieldBlock literal stride link g x.2 x.1 = (u,s)}, pieceWidth _ _ x.val.2) ≤ g := by
  exact width_per_block (ends := physicalEnds R r) (literal := literal) (stride := stride) (link := link) (g := g)
    fits hg u s

/-- Counting both ends of each physical exterior bit gives exactly the per-team
link incidence summed over the teams. -/
theorem twice_physical_width :
    2 * (∑ c : Pieces (fieldStart (R := R) (r := r) literal stride link) g link, pieceWidth _ _ c) =
      (R+1)*(r*R*link) := by
  have h := Fintype.card_congr (endpointEquiv R)
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at h
  rw [sum_pieceWidth,Fintype.card_prod,Fintype.card_fin]
  calc
    2 * (Fintype.card (Routing.Block (R+1)) * r * link) =
      (2 * Fintype.card (Routing.Block (R+1))) * r * link := by ring
    _ = _ := by rw [h]; ring

variable {D : ℕ} {P Free : Type} {N : Network D P (fun _ => 1)}
variable (B : Bundle N Free (Pieces (fieldStart (R := R) (r := r) literal stride link) g link)
    (pieceWidth _ _))

/-- Exact bound on the two kinds of exterior cable records at a concrete initial
block, even when the endpoint carrying the corresponding fine input is renamed. -/
theorem Bundle.physical_endRecords (block : N.Site → Fin (R+1) × ℕ)
    (stored : ∀ c a, block (B.endpoint c a) = fieldBlock literal stride link g c a)
    (fits : R*link ≤ stride) (hg : 0 < g) (small : g ≤ link) (u : Fin (R+1)) (s : ℕ)
    (expanded : Bool) :
    B.endRecords expanded (fun v => block v = (u,s)) ≤ 4 + if expanded then g else 0 := by
  let A := Bool × Pieces (fieldStart (R := R) (r := r) literal stride link) g link
  let pred (x : A) := fieldBlock literal stride link g x.2 x.1 = (u,s)
  have he : B.endRecords expanded (fun v => block v = (u,s)) =
      ∑ x : {x : A // pred x}, recordCost expanded (pieceWidth _ _ x.val.2) := by
    unfold Bundle.endRecords testedWidth
    simp only [stored]
    rw [← sum_filter]
    apply sum_subtype (p := pred)
    intro x
    simp only [mem_filter,mem_univ,true_and,pred]
  have hc := physical_ends_per_block (r := r) literal stride link g fits hg small u s
  have hw := physical_width_per_block (r := r) literal stride link g fits hg u s
  rw [he]
  have hn : Fintype.card {x : A // pred x} ≤ 4 := by simpa only [Fintype.card_subtype] using hc
  cases expanded
  · change (∑ _ : {x : A // pred x}, (1 : ℕ)) ≤ 4 + 0
    simpa only [sum_const,card_univ,nsmul_one,Nat.cast_id,Nat.add_zero] using hn
  · change (∑ x : {x : A // pred x}, (1 + pieceWidth _ _ x.val.2)) ≤ 4 + g
    rw [sum_add_distrib,sum_const,card_univ,nsmul_one,Nat.cast_id]
    exact Nat.add_le_add hn hw

/-- When the shortened internal cables fit the normalized budget and each team's
physical exterior incidence fits `X₀`, all intercell cables fit the bound of
Proposition 7.2(i). -/
theorem Bundle.physical_intercell_le {C : Type*} (cell : N.Site → C) (X₀ : ℕ)
    (inside : intercellWidth N cell ≤ (R+1)*X₀) (exterior : r*R*link ≤ X₀) :
    intercellWidth B.layout cell ≤ 2*(R+1)*X₀ := by
  have h := twice_physical_width (R := R) (r := r) literal stride link g
  have hb := Nat.mul_le_mul_left (R+1) exterior
  have hi := B.intercell_le cell
  rw [show 2*(R+1)*X₀ = 2*((R+1)*X₀) by ring]
  omega

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
