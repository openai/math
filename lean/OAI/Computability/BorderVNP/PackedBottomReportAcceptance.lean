import OAI.Computability.BorderVNP.PackedBottomScalarWiring
import OAI.Computability.BorderVNP.PackedBottomNamedReads

/-! # Exact acceptance of an original weighted box and its report supplement

The local native reader and the sparse use links accept precisely the original
fine guards on the completed work assignment and the public channel zero tests.
This statement treats every false use and every unused lane explicitly.
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
local notation "ord" => sourceOrder G channelID groupID v
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "rows₀" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "s₀" => slab (H := H) (src := src) (dst := dst) N cell position width owner siteID edgeID portID v rules
local notation "birth" => born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "slice₀" => copyInput (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
local notation "padAddr" => channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
local notation "Pad" => publicPad N cell position pack width owner channelID groupID v

omit [Fintype C] in
private theorem namedPass (bank : ℕ → Bool) (boxes : List (List Factor)) (use : Port → Bool)
    (copies stride next cursor : ℕ) (i : Fin copies)
    (linksPass : ∀ r ∈ links 0 stride copies cursor (sidecar next fs), r.Valid boxes bank)
    (names : NamedAt bank use copies i.val cursor (sidecar next fs)) :
    (∀ f ∈ stage next fs, (f.observe bank (i.val*stride) i.val).isSome = true) ↔
      ∀ w : {u : N.Site // cell u = v}, (rules w).passes
        (fun l => bank (i.val*stride+(GridBoxes.lane N cell v edgeID portID w l).val)) use = true := by
  have hh := staged_grid_reads N cell v siteID edgeID portID rules bank boxes use 0 stride copies
    i.val next cursor i.isLt linksPass names
  simp only [Nat.zero_add] at hh
  let pred := fun (a : Option (Bool × Option ℕ)) => a.isSome = true
  have hp := congrArg (fun xs => ∀ x ∈ xs, pred x) hh
  simp only [List.forall_mem_map,pred,mem_siteList,forall_true_left] at hp
  rw [hp]
  apply forall_congr'
  intro w
  cases he : (rules w).passes (fun l => bank (i.val*stride+(GridBoxes.lane N cell v edgeID portID w l).val)) use <;>
    simp

/-- Reading the immutable staged factors at each physical offset is equivalent to
the intended original fine checks, provided the native use reports resolve the
actual names. All three classes of private wiring/padding factors are also tested. -/
theorem complete_acceptance (copies capFine capReport cursor : ℕ)
    (hf : GridBoxes.stride N cell v ≤ capFine) (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (bank : ℕ → Bool) (boxes : List (List Factor)) (use : Fin copies → Port → Bool) :
    let s := s₀ capFine capReport hf hc
    let input := slice₀ copies s.stride bank
    let supp := ∀ r ∈ reportRows 0 s.orig capReport copies cursor fs, r.Valid boxes bank
    (∀ i : Fin copies, NamedAt bank (use i) copies i.val cursor (sidecar s.orig fs)) →
    (( ((birth copies capFine capReport).observe bank).isSome = true ∧ supp) ↔
      ((∀ i : Fin copies, s.Checks (fun k => bank (i.val*s.stride+k))
        (fun k => input i (fineIndex k)) (input i) (fun k => bank (cursor+k.val*copies+i.val))) ∧
       (∀ i : Fin copies, Pad (input i)) ∧
       ∀ (i : Fin copies) (w : {u : N.Site // cell u = v}), (rules w).passes
         (fun l => bank (i.val*s.stride+(GridBoxes.lane N cell v edgeID portID w l).val)) (use i) = true)) := by
  intro s input supp names
  let box := rows₀ capFine capReport
  have hs : s.stride = bottomStride s.orig capReport := rfl
  have su : s.used = count fs := rfl
  have sc : s.capFine = capFine := rfl
  have hbase := BottomRepeat.bornWith_accepts G channelID groupID v copies capFine s.stride box bank
  have ht := public_ties_iff (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID
    v copies capFine s.stride [box] bank
  have hl (h : supp) : ∀ r ∈ links 0 s.stride copies cursor (sidecar s.orig fs), r.Valid boxes bank := by
    rw [hs]
    exact fun r hr => h r (List.mem_append_left _ hr)
  have hn (h : supp) (i : Fin copies) := namedPass N cell siteID edgeID portID v rules bank boxes (use i)
    copies s.stride s.orig cursor i (hl h) (names i)
  have pd (i : Fin copies)
      (hpub : ∀ j : Fin (incoming G v), bank (i.val*s.stride+capFine+j.val) = input i j) :
      (∀ f ∈ GridPadding.factors pack v (padAddr capFine), (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔
        Pad (input i) := by
    rw [← List.all_eq_true]
    apply GridPadding.factors_pass
    intro l
    simpa only [channelAddress,Nat.add_assoc] using hpub (ord (.inl ⟨l.1,l.2⟩))
  constructor
  · rintro ⟨ok,h⟩
    have hb := hbase.mp ok
    have hp := ht.mp hb.1
    refine ⟨fun i => accepted_checks N cell position pack width owner lane aligned siteID edgeID portID
      channelID groupID v rules copies capFine capReport cursor hf hc bank boxes i ok h,?_,?_⟩
    · intro i
      apply (pd i (hp i)).mp
      intro f hm
      exact hb.2 i i.isLt f (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hm)))
    · intro i
      apply (hn h i).mp
      intro f hm
      exact hb.2 i i.isLt f (List.mem_append_left _ (List.mem_append_left _ hm))
  · rintro ⟨checks,hpad,hfine⟩
    have hp (i : Fin copies) (j : Fin (incoming G v)) : bank (i.val*s.stride+capFine+j.val) = input i j := by
      simpa only [sc,Nat.add_assoc] using (checks i).2.2.1 j
    have h : supp := by
      apply (reportRows_valid bank boxes 0 s.orig capReport copies cursor fs s.reportFits).mpr
      intro i hi t htc
      by_cases hw : t < count fs
      · have hh := (checks ⟨i,hi⟩).2.2.2.1 ⟨t,hw⟩
        simpa only [stageValue,ite_eq_left hw,Nat.zero_add,hs,Nat.add_assoc] using hh
      · have htc' : t-count fs < capReport-count fs := by omega
        have hh := (checks ⟨i,hi⟩).2.2.2.2 (t-count fs) htc'
        have add : count fs+(t-count fs) = t := Nat.add_sub_of_le (Nat.le_of_not_lt hw)
        simpa only [stageValue,ite_eq_right hw,Nat.zero_add,hs,su,Nat.add_assoc,add] using hh
    refine ⟨hbase.mpr ⟨ht.mpr hp,?_⟩,h⟩
    intro i hi
    let c : Fin copies := ⟨i,hi⟩
    change ∀ f ∈ rows₀ capFine capReport, (f.observe bank (i*s.stride) i).isSome = true
    simp only [stored,wiring,List.forall_mem_append]
    refine ⟨⟨(hn h c).mpr (hfine c),⟨⟨?_,?_⟩,(pd c (hp c)).mpr (hpad c)⟩⟩,?_⟩
    · rw [← List.all_eq_true,fineTies_pass]
      intro j
      exact ((checks c).1 j).trans (by simpa only [Nat.add_assoc] using (hp c (fineIndex j)).symm)
    · rw [← List.all_eq_true,fineZeros_pass]
      exact (checks c).2.1
    · rw [← List.all_eq_true,reportZeros_pass]
      exact (checks c).2.2.2.2

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
