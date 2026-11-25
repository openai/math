import OAI.Computability.BorderVNP.PackedBottomSiteForced

/-! # Canonical work assignments for original sites with field-valued factors

For scalar source boxes no weighted report region is needed. The same private
fine-to-public ties and padding factors still describe exactly the original
hidden wires and the true public grid padding predicate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "ord" => sourceOrder G channelID groupID v
local notation "W" => wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "ft" => fineTies N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "slice₀" => copyInput (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v

/-- Public original-box capacity in the scalar specialization. -/
noncomputable def scalarSlab (capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine) : Slab :=
  ⟨guessedSize N cell v,suppliedSize N cell v,capFine,incoming G v,0,0,fit,le_rfl⟩

local notation "s₀" => scalarSlab (src := src) (dst := dst) (H := H) N cell position width owner v

private theorem pairValue {m n : ℕ} (i : Fin m) (k : Fin n) :
    (finProdFinEquiv (i,k)).val = i.val*n+k.val := by change k.val+n*i.val = _; ac_rfl

omit [Fintype P] in
/-- The public repeated interval records pass exactly when the staged full-grid
incidence array equals every copy slice of the current grouped input. -/
theorem public_ties_iff (copies capFine stride : ℕ) (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r ∈ BottomRepeat.ties G channelID groupID v copies capFine stride, r.Valid boxes bank) ↔
      ∀ i : Fin copies, ∀ j : Fin (incoming G v),
        bank (i.val*stride+capFine+j.val) = slice₀ copies stride bank i j := by
  constructor
  · intro hh i j
    have h := BottomRepeat.tie_reads G channelID groupID v copies capFine stride boxes bank hh i ((ord).symm j)
    rw [(ord).apply_symm_apply] at h
    exact h
  · intro h
    apply (BottomRepeat.ties_valid G channelID groupID v copies capFine stride boxes bank).mpr
    intro row i k
    rcases row with e | p
    · change Fin ((G).width e.val) at k
      have hh := h i (ord (.inl ⟨e,k⟩))
      simp only [copyInput,Equiv.symm_apply_apply,BottomRepeat.repeatInput,wireOrdinal G channelID groupID v e k,
        wireOrdinal (BottomRepeat.wide G copies) channelID groupID v e (finProdFinEquiv (i,k)),pairValue i k] at hh
      simpa only [BottomRepeat.oneStart,BottomRepeat.wideStart,BottomRepeat.rowWidth,Sum.elim_inl,Nat.add_assoc]
        using hh
    · change Fin (width p.val) at k
      have hh := h i (ord (.inr ⟨p,k⟩))
      simp only [copyInput,Equiv.symm_apply_apply,BottomRepeat.repeatInput,portOrdinal G channelID groupID v p k,
        portOrdinal (BottomRepeat.wide G copies) channelID groupID v p (finProdFinEquiv (i,k)),pairValue i k] at hh
      simpa only [BottomRepeat.oneStart,BottomRepeat.wideStart,BottomRepeat.rowWidth,Sum.elim_inr,Nat.add_assoc]
        using hh

/-- The exact public cable padding condition on a compact one-copy grouped input. -/
def publicPad (input : Fin (incoming G v) → Bool) : Prop :=
  ∀ q : {q : Q // src q = v ∨ dst q = v}, pack.ZeroPad q.val (fun k => input (ord (.inl ⟨q,k⟩)))

/-- The complete physical wiring and padding checks, with no report lanes, are
exactly the canonical hidden-wire extension and the channel padding test. -/
theorem nonreport_wiring_iff (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine)
    (bank : ℕ → Bool) (boxes : List (List Factor)) :
    let s := s₀ capFine fit
    let input := slice₀ copies s.stride bank
    ( (∀ r ∈ BottomRepeat.ties G channelID groupID v copies capFine s.stride, r.Valid boxes bank) ∧
      ∀ i : Fin copies, ∀ f ∈ W capFine, (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔
    ( (∀ i : Fin copies, s.Checks (fun j => bank (i.val*s.stride+j)) (fun k => input i (fineIndex k))
          (input i) Fin.elim0) ∧
      ∀ i : Fin copies, publicPad N cell position pack width owner channelID groupID v (input i)) := by
  intro s input
  let qAddr := channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v capFine
  let Pad := GridPadding.factors pack v qAddr
  let Zero := fineZeros (GridBoxes.stride N cell v) capFine
  have pub := public_ties_iff (H := H) (src := src) (dst := dst) N cell position width owner channelID groupID
    v copies capFine s.stride boxes bank
  have sub (i : Fin copies) :
      (∀ f ∈ W capFine, (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔
        ((ft capFine).all (fun f => (f.observe bank (i.val*s.stride) i.val).isSome) = true ∧
         Zero.all (fun f => (f.observe bank (i.val*s.stride) i.val).isSome) = true) ∧
         Pad.all (fun f => (f.observe bank (i.val*s.stride) i.val).isSome) = true := by
    simp only [wiring,List.forall_mem_append,List.all_eq_true,Zero,Pad,qAddr]
  have pd (i : Fin copies)
      (hpub : ∀ j : Fin (incoming G v), bank (i.val*s.stride+capFine+j.val) = input i j) :
      (Pad.all (fun f => (f.observe bank (i.val*s.stride) i.val).isSome)) = true ↔
        publicPad N cell position pack width owner channelID groupID v (input i) :=
    GridPadding.factors_pass pack v qAddr (fun q k => input i (ord (.inl ⟨q,k⟩))) bank (i.val*s.stride)
      i.val (fun l => by simpa only [qAddr,channelAddress,Nat.add_assoc] using hpub (ord (.inl ⟨l.1,l.2⟩)))
  rw [pub]
  constructor
  · rintro ⟨hp,hw⟩
    refine ⟨?_,fun i => (pd i (hp i)).mp ((sub i).mp (hw i)).2⟩
    intro i
    obtain ⟨⟨hu,hz⟩,_⟩ := (sub i).mp (hw i)
    have ft' := (fineTies_pass N cell position pack width owner lane aligned edgeID portID channelID groupID
      v capFine (i.val*s.stride) i.val bank).mp hu
    have hz' := (fineZeros_pass _ capFine (i.val*s.stride) i.val bank).mp hz
    refine ⟨fun k => (ft' k).trans (by simpa only [Nat.add_assoc] using hp i (fineIndex k)),hz',?_,
      fun j => Fin.elim0 j,fun k hk => (Nat.not_lt_zero k hk).elim⟩
    intro j
    change bank (i.val*s.stride+(capFine+j.val)) = input i j
    simpa only [Nat.add_assoc] using hp i j
  · rintro ⟨hc,hpad⟩
    have hp (i : Fin copies) (j : Fin (incoming G v)) : bank (i.val*s.stride+capFine+j.val) = input i j := by
      have hh := (hc i).2.2.1 j
      change bank (i.val*s.stride+(capFine+j.val)) = input i j at hh
      simpa only [Nat.add_assoc] using hh
    refine ⟨hp,?_⟩
    intro i
    apply (sub i).mpr
    refine ⟨⟨?_,(fineZeros_pass _ capFine (i.val*s.stride) i.val bank).mpr (hc i).2.1⟩,
      (pd i (hp i)).mpr (hpad i)⟩
    apply (fineTies_pass N cell position pack width owner lane aligned edgeID portID channelID groupID
      v capFine (i.val*s.stride) i.val bank).mpr
    intro j
    exact ((hc i).1 j).trans (by simpa only [Nat.add_assoc] using (hp i (fineIndex j)).symm)

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
