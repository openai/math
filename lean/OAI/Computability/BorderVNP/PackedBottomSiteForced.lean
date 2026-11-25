import OAI.Computability.BorderVNP.PackedBottomBoxInterpreter
import OAI.Computability.BorderVNP.PackedBottomBankLanes

/-! # A passing original site has exactly its extracted fine wire assignment

The actual private truth tables supply the fine-to-public equalities and fine
padding tests. Public ties identify the copy-major staged inputs with the
true grouped cable and port slices. The supplemental rows identify the report
lanes with the compact external guesses. This derives the full work-slab
condition from the checked record interpreter.
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
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "rows₀" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "s₀" => slab (H := H) (src := src) (dst := dst) N cell position width owner siteID edgeID portID v rules
local notation "birth" => born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v

/-- Canonical single-copy public input read from the actual repeated cable or grouped
port in the current site's physical incidence suffix. -/
noncomputable def copyInput (copies stride : ℕ) (bank : ℕ → Bool) (i : Fin copies) (k : Fin (incoming G v)) : Bool :=
  bank (copies*stride+(sourceOrder (BottomRepeat.wide G copies) channelID groupID v
    (BottomRepeat.repeatInput G v copies i ((sourceOrder G channelID groupID v).symm k))).val)

local notation "slice₀" => copyInput (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v

/-- A real accepted original-box call satisfies every lane equation required by the
bijection from original fine wire guesses. The full private work-vector prefix and
current public suffix share the same site-local bank in this statement. -/
theorem accepted_checks (copies capFine capReport cursor : ℕ)
    (hf : GridBoxes.stride N cell v ≤ capFine) (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (bank : ℕ → Bool) (boxes : List (List Factor)) (i : Fin copies) :
    let s := s₀ capFine capReport hf hc
    let input := slice₀ copies s.stride bank i
    ((birth copies capFine capReport).observe bank).isSome = true →
    (∀ r ∈ reportRows 0 s.orig capReport copies cursor fs, r.Valid boxes bank) →
    s.Checks (fun k => bank (i.val*s.stride+k)) (fun k => input (fineIndex k)) input
      (fun k => bank (cursor+k.val*copies+i.val)) := by
  intro s input pass supplemental
  let raw := rows₀ capFine capReport
  have h := (BottomRepeat.bornWith_accepts G channelID groupID v copies capFine s.stride raw bank).mp pass
  have rowOK := h.2 i.val i.isLt
  have hs : s.stride = bottomStride s.orig capReport := rfl
  have sc : s.capFine = capFine := rfl
  have su : s.used = count fs := rfl
  have inputRead (j : Fin (incoming G v)) : bank (i.val*s.stride+capFine+j.val) = input j := by
    have hj := BottomRepeat.tie_reads G channelID groupID v copies capFine s.stride [raw] bank h.1 i
      ((sourceOrder G channelID groupID v).symm j)
    rw [(sourceOrder G channelID groupID v).apply_symm_apply] at hj
    exact hj
  have tiesOK : (fineTies N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine).all
      (fun f => (f.observe bank (i.val*s.stride) i.val).isSome) = true := by
    apply List.all_eq_true.mpr
    intro f hm
    apply rowOK
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hm)))
  have zerosOK : (fineZeros (GridBoxes.stride N cell v) capFine).all
      (fun f => (f.observe bank (i.val*s.stride) i.val).isSome) = true := by
    apply List.all_eq_true.mpr
    intro f hm
    apply rowOK
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hm)))
  have hu := (fineTies_pass N cell position pack width owner lane aligned edgeID portID channelID groupID v
    capFine (i.val*s.stride) i.val bank).mp tiesOK
  have hz := (fineZeros_pass (GridBoxes.stride N cell v) capFine (i.val*s.stride) i.val bank).mp zerosOK
  have reports := (reportRows_valid bank boxes 0 s.orig capReport copies cursor fs s.reportFits).mp supplemental i.val i.isLt
  refine ⟨fun j => (hu j).trans (by simpa only [Nat.add_assoc] using inputRead (fineIndex j)),
    hz,fun j => by simpa only [sc,Nat.add_assoc] using inputRead j,?_,?_⟩
  · intro j
    have hj : j.val < count fs := j.isLt
    have hh := reports j.val (lt_of_lt_of_le hj s.reportFits)
    simpa only [hs,stageValue,ite_eq_left hj,Nat.zero_add,Nat.add_assoc] using hh
  · intro k hk
    have hc' : count fs ≤ capReport := s.reportFits
    have hk' : count fs+k < capReport := by change k < capReport-count fs at hk; omega
    have hh := reports (count fs+k) hk'
    simpa only [hs,su,stageValue,Nat.not_lt.mpr (Nat.le_add_right (count fs) k),ite_false,
      Nat.zero_add,Nat.add_assoc] using hh

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
