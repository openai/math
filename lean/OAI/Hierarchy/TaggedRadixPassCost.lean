import OAI.Hierarchy.TaggedPassShell
import OAI.Hierarchy.TaggedRadixPassVolume

namespace OAI
/-! # Physical cost of one packed radix pass

The banked local cells are counted once per physical block. The global sort
compares pack words, with the factor from their width charged to the total
number of physical lanes. The five intermediate arrays and all static
scatter cells are included.
-/

noncomputable section
namespace Hierarchy.Tagged.Radix.PassShape

open ThreeFlat Routing SortNetwork RadixStage
open scoped BigOperators Classical

private abbrev bill {F : Type*} {p : ℕ} (N : BitNetwork F p) := N.cells+N.internal

private theorem joined_bill {F : Type*} {I M O H J : Type} [Fintype I] [Fintype M] [Fintype O]
    [Fintype H] [Fintype J] (N : Network F I M H) (P : Network F M O J) :
    bill (seq N P) = bill N + bill P + Fintype.card M := by
  unfold bill
  rw [seq_cells N P, seq_internal N P]
  omega

private theorem parallel_bill {F : Type*} {I O : Type} [Fintype I] [Fintype O] {q : ℕ}
    (n : ℕ) (N : Network F I O (Fin q)) :
    bill (parallel (fun _ : Fin n => N)) = n*bill N := by
  unfold bill
  rw [parallel_cells (fun _ : Fin n => N), parallel_internal (fun _ : Fin n => N)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.mul_add]

/-- The three local intermediate arrays and two packed ones are counted at
the five composition boundaries, independently of the stages' own wiring. -/
private theorem sequence_bill {F : Type*} {I D W O H A G : Type} [Fintype I] [Fintype D]
    [Fintype W] [Fintype O] [Fintype H] [Fintype A] [Fintype G]
    (enter : Network F I D Empty) (sort : Network F D D H) (align : Network F D D A)
    (pack : Network F D W Empty) (wideSort : Network F W W G) (leave : Network F W O Empty) :
    bill (seq (seq (seq (seq (seq enter sort) align) pack) wideSort) leave) =
      bill enter + bill sort + bill align + bill pack + bill wideSort + bill leave +
        3*Fintype.card D + 2*Fintype.card W := by
  let ab : Network F I D (Empty ⊕ H) := seq enter sort
  let abc : Network F I D ((Empty ⊕ H) ⊕ A) := seq ab align
  let abcd : Network F I W (((Empty ⊕ H) ⊕ A) ⊕ Empty) := seq abc pack
  let abcde : Network F I W ((((Empty ⊕ H) ⊕ A) ⊕ Empty) ⊕ G) := seq abcd wideSort
  have b₂ : bill ab = bill enter + bill sort + Fintype.card D := joined_bill enter sort
  have b₃ : bill abc = bill ab + bill align + Fintype.card D := joined_bill ab align
  have b₄ : bill abcd = bill abc + bill pack + Fintype.card D := joined_bill abc pack
  have b₅ : bill abcde = bill abcd + bill wideSort + Fintype.card W := joined_bill abcd wideSort
  change bill (seq abcde leave) = _
  rw [joined_bill abcde leave, b₅, b₄, b₃, b₂]
  omega

private theorem sort_bill (F : Type*) [Zero F] [One F] {a w d : ℕ} (digit : Fin d → Fin w) :
    bill (SortRelation.shell (h := a) F digit) ≤ 1024*2^a*(a+d+w+1) := by
  refine (SortRelation.size (h:=a) F digit).trans ?_
  exact sort_shell_width_cost (2^a) a d w

private theorem align_bill (F : Type*) [Zero F] [One F] {j t w d : ℕ}
    (real : Fin w) (digit : Fin d → Fin w) :
    bill (AlignShell.shell (AlignRows.network (j := j) (t := t) F real digit)) ≤
      15000000000*2^(j+t)*(d+(j+t)+w+3) := by
  unfold bill
  rw [AlignShell.size]
  refine (Nat.add_le_add_right (Nat.add_le_add_right (AlignRows.size (j:=j) (t:=t) F real digit) _) _).trans ?_
  exact align_shell_width_cost (2^(j+t)) j t d w

/-- The bound includes the entire output array retained for the following pass. -/
theorem network_cost (F : Type*) [Zero F] [One F] (s : PassShape) {h c w : ℕ}
    (dummy : Bits w) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)
    (localVolume : s.blocks*2^s.localBits ≤ 8*2^h)
    (wideVolume : 2^s.globalHeight*s.pack ≤ 8*2^h) (lastVolume : s.nextRows ≤ 4*2^h)
    (hd : s.digitBits ≤ c*h) (hl : s.localBits ≤ c*h) (hg : s.globalHeight ≤ c*h)
    (hw : w ≤ c*h) :
    (network F s dummy real isDummy digit).cells + (network F s dummy real isDummy digit).internal +
        Fintype.card (RowBits s.nextRows w) ≤ (1000000000000*c)*2^h*h := by
  let L := s.blocks*2^s.localBits
  let W := 2^s.globalHeight*s.pack
  let S := SortRelation.shell (h := s.localBits) F (maskedDigit digit isDummy)
  let A := AlignShell.shell (AlignRows.network (j := s.packBits) (t := s.upperBits) F real digit)
  let G := SortRelation.shell (h := s.globalHeight) F (s.wideDigit digit isDummy)
  have ledger :
      (network F s dummy real isDummy digit).cells + (network F s dummy real isDummy digit).internal +
        Fintype.card (RowBits s.nextRows w) =
          s.blocks*bill S + s.blocks*bill A + bill G + 4*(L*w) + 3*(W*w) + 2*(s.nextRows*w) := by
    let D := SortRelation.Data s.localBits w
    let sort : Network F (s.LocalData w) (s.LocalData w) (Fin (s.sourceArity w)) :=
      parallel (fun _ : Fin s.blocks => S)
    let align : Network F (s.LocalData w) (s.LocalData w) (Fin (s.alignArity w)) :=
      parallel (fun _ : Fin s.blocks => A)
    have bs : bill sort = s.blocks * bill S :=
      parallel_bill (I:=D) (O:=D) (q:=pins s.localBits (s.localBits+w)) s.blocks S
    have ba : bill align = s.blocks * bill A :=
      parallel_bill (I:=D) (O:=D) (q:=pins s.localBits w) s.blocks A
    have total := sequence_bill (I:=RowBits s.rows w) (D:=s.LocalData w) (W:=s.WideData w)
      (O:=RowBits s.nextRows w) (H:=Fin (s.sourceArity w)) (A:=Fin (s.alignArity w)) (G:=Fin (s.wideArity w))
      (scatterNetwork F (s.enter dummy)) sort align (scatterNetwork F (s.wideInput dummy)) G (scatterNetwork F s.leave)
    change bill (network F s dummy real isDummy digit) + _ = _
    calc
      _ = _ := congrArg (fun z => z + Fintype.card (RowBits s.nextRows w)) total
      _ = _ := by
        rw [bs, ba]
        simp only [bill, scatter_cells, scatter_internal, Nat.add_zero, LocalData, WideData, SortRelation.Data,
          Payload, RowBits, Fintype.card_prod, Fintype.card_fin, L, W]
        ring
  rw [ledger]
  exact s.ledger_cost (by have := real.isLt; omega) localVolume wideVolume lastVolume
    hd hl hg hw (sort_bill (a:=s.localBits) F (maskedDigit digit isDummy))
    (align_bill (j:=s.packBits) (t:=s.upperBits) F real digit)
    (sort_bill (a:=s.globalHeight) F (s.wideDigit digit isDummy))


end Hierarchy.Tagged.Radix.PassShape


namespace Hierarchy.Tagged.Radix

open ThreeFlat RadixStage

/-- On the actual pass schedule, one constant pays for every intermediate
stage and its complete outgoing row array. -/
theorem GridScales.pass_network_cost {a B : ℝ} {h n c w : ℕ} (g : GridScales a B h)
    (two : 2 ≤ h) (count : n+1 ≤ 2^(passBits h)) (width : w ≤ c*h)
    (F : Type*) [Zero F] [One F] (i : ℕ) (dummy : Bits w) (real isDummy : Fin w)
    (digit : Fin (digitBits a h) → Fin w) :
    let s := passShapeAt a B h n i
    (s.network F dummy real isDummy digit).cells + (s.network F dummy real isDummy digit).internal +
        Fintype.card (RowBits s.nextRows w) ≤ (1000000000000*(c+2))*(2^h*h) := by
  let s := passShapeAt a B h n i
  obtain ⟨lv,wv,ov,dk,lk,gk⟩ := g.pass_network_resources (c:=c) two count i (ell:=s.localBits) rfl
  have wd : w ≤ (c+2)*h := by rw [Nat.add_mul]; omega
  exact (s.network_cost F dummy real isDummy digit lv wv ov dk lk gk wd).trans_eq (by ring)


end Hierarchy.Tagged.Radix

end
end OAI
