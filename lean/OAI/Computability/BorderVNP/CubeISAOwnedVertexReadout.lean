import OAI.Computability.BorderVNP.CubeISAOwnedVertexRow

/-! # Recovering the physical origin of every emitted vertex record

The compact packet rank counts successful earlier trials. Multiplying it
by the half-cube size and adding the local vertex rank gives the triple's
actual location in the owned directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.Owned Cube.Physical.VertexIndex Finset

variable {n d blocks : ℕ}

private theorem retain (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) {k l : ℕ} (hkl : k ≤ l) :
    let st := rowImage (blocks := blocks) i pair high base stride width out initial
    (st k).1 ≤ (st l).1 ∧ ∀ a < (st k).1, (st l).2 a = (st k).2 a := by
  induction hkl with
  | refl => exact ⟨le_rfl,fun _ _ => rfl⟩
  | @step l _ ih =>
    dsimp only at ih ⊢
    rw [rowImage]
    cases h : packetAtNat (blocks := blocks) i pair l with
    | none => exact ih
    | some p =>
      refine ⟨Nat.le_add_right_of_le ih.1,fun a ha => ?_⟩
      exact (image_outside _ _ _ _ _ _ _ a (.inl (ha.trans_le ih.1))).trans (ih.2 a ha)

/-- In the completed row, the three words at each dense rank are the bank of
the specified packet, its stored selector, and the canonical index of the
specified vertex at the local grouping symbol. -/
theorem rowImage_at (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride width out : ℕ)
    (initial : ℕ → ℕ) (t : Fin (packetTrials n d blocks)) (h : packetTrialValid t) (j : Fin (2^n)) :
    let p := (packetRowEquiv i pair ⟨t,h⟩).val
    let bank := bankAt base stride p
    let sel := (SelectorRead.decoded initial bank width).val
    let a := out+3*(selectedPrefix (blocks := blocks) i pair t.val * 2^n+j.val)
    let M := (rowImage (blocks := blocks) i pair high base stride width out initial (packetTrials n d blocks)).2
    M a = bank ∧ M (a+1) = sel ∧ M (a+2) = (Tally.vertexOrder (n+1) (owned p i high j).val).val := by
  intro p bank sel a M
  let img := rowImage (blocks := blocks) i pair high base stride width out initial
  let v := img t.val
  have here : img (t.val+1) = appendPacket i high base stride width initial p v := by
    dsimp only [img]
    rw [rowImage, (selected_fields i pair t h).1]
  have ca : a = v.1+3*j.val := by
    dsimp only [a,v,img]
    rw [rowImage_cursor]
    ring
  have keep : ∀ a < (img (t.val+1)).1, (img (packetTrials n d blocks)).2 a = (img (t.val+1)).2 a :=
    (retain (blocks := blocks) i pair high base stride width out initial (k := t.val+1) (l := packetTrials n d blocks) t.isLt).2
  have below : a+2 < (img (t.val+1)).1 := by
    rw [here,ca]
    change _ < v.1+3*2^n
    have := j.isLt
    omega
  change (img _).2 a = _ ∧ (img _).2 (a+1) = _ ∧ (img _).2 (a+2) = _
  rw [keep a (by omega),keep (a+1) (by omega),keep (a+2) below,here,ca]
  obtain ⟨x,y,_⟩ := image_at j.isLt v.1 bank sel (2^i.val) (ownerBit i p.1.2 high).toNat v.2
  exact ⟨x,y,image_vertex p i high j v.1 bank sel v.2⟩

private theorem prefix_mono (i : Fin (n+1)) (pair : Symbols d) {k l : ℕ} (h : k ≤ l) :
    selectedPrefix (blocks := blocks) i pair k ≤ selectedPrefix (blocks := blocks) i pair l :=
  sum_le_sum_of_subset_of_nonneg (range_mono h) fun _ _ _ => Nat.zero_le _

/-- The counter's emitted prefix ranks enumerate every compact packet slot
exactly once. The inverse exists because the strict row cardinality is exact. -/
noncomputable def densePacketEquiv (i : Fin (n+1)) (pair : Symbols d) :
    {t : Fin (packetTrials n d blocks) // packetTrialValid t} ≃ Fin (2*blocks*(d.choose 2)^n) := by
  let rank (t : {t : Fin (packetTrials n d blocks) // packetTrialValid t}) : Fin (2*blocks*(d.choose 2)^n) :=
    ⟨selectedPrefix (blocks := blocks) i pair t.val.val,selectedPrefix_capacity i pair t.val t.property⟩
  refine Equiv.ofBijective rank ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_,?_⟩)
  · intro x y e
    have strict (u v : {t : Fin (packetTrials n d blocks) // packetTrialValid t}) (h : u.val < v.val) :
        (rank u).val < (rank v).val := by
      have step : selectedPrefix (blocks := blocks) i pair (u.val.val+1) =
          selectedPrefix (blocks := blocks) i pair u.val.val+1 := by
        unfold selectedPrefix
        rw [sum_range_succ, (selected_fields i pair u.val u.property).1]
        rfl
      have le := prefix_mono (blocks := blocks) i pair (k := u.val.val+1) (l := v.val.val) h
      change selectedPrefix (blocks := blocks) i pair u.val.val < _
      rwa [step] at le
    obtain h | h | h := lt_trichotomy x.val y.val
    · exact ((strict x y h).ne (congrArg Fin.val e)).elim
    · exact Subtype.ext h
    · exact ((strict y x h).ne (congrArg Fin.val e.symm)).elim
  · exact (Fintype.card_congr (packetRowEquiv i pair)).trans ((card_packets_row i pair).trans (Fintype.card_fin _).symm)

/-- The equivalence uses the numeric prefix seen by the executable loop. -/
theorem densePacketEquiv_val (i : Fin (n+1)) (pair : Symbols d)
    (t : {t : Fin (packetTrials n d blocks) // packetTrialValid t}) :
    (densePacketEquiv i pair t).val = selectedPrefix (blocks := blocks) i pair t.val.val := rfl

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
