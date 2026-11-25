import OAI.Computability.BorderVNP.PackedBottomDynamicGuess
import OAI.Computability.BorderVNP.PackedBottomSelectedReports
import OAI.Computability.BorderVNP.PackedBottomBoxCharges
import OAI.Computability.BorderVNP.FiniteBottomGridModel

/-! # Ordinary guard value of the weighted original site

Before a final cell checks externally named uses, each private report is
already forced by its selected fine wire. Reindexing the private work sum
therefore counts each passing fine assignment once. All observations in
this immutable box have the positive sign and carry no gadget position.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical
open private bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ w : {u : N.Site // cell u = v}, Rule N w.val)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "W" => wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "s₀" => slab (H := H) (src := src) (dst := dst) N cell position width owner siteID edgeID portID v rules
local notation "birth" => born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "box₀" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
local notation "idx" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "slice₀" => scalarSlice (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
local notation "fine₀" => scalarFine N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "pad" => publicPad N cell position pack width owner channelID groupID v

private def HeadChecks (s : Slab) (read : ℕ → Bool) (u : Fin s.supplied → Bool) (x : Fin s.incoming → Bool) : Prop :=
  (∀ j : Fin s.supplied, read (s.guessed+j.val) = u j) ∧
  (∀ j < s.capFine-(s.guessed+s.supplied), read (s.guessed+s.supplied+j) = false) ∧
  ∀ j : Fin s.incoming, read (s.capFine+j.val) = x j

private theorem heads (copies capFine capReport : ℕ)
    (hf : GridBoxes.stride N cell v ≤ capFine) (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool) (work : Fin (copies*(s₀ capFine capReport hf hc).stride) → Bool)
    (boxes : List (List Factor)) :
    let s := s₀ capFine capReport hf hc
    let bank := bits work input
    ((∀ r ∈ BottomRepeat.ties G channelID groupID v copies capFine s.stride, r.Valid boxes bank) ∧
      ∀ i : Fin copies, ∀ f ∈ W capFine, (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔
    (∀ i : Fin copies, HeadChecks s (fun j => bank (i.val*s.stride+j)) (fine₀ copies input i) (slice₀ copies input i)) ∧
      ∀ i, pad (slice₀ copies input i) := by
  intro s bank
  have sc : s.capFine = capFine := rfl
  let x := slice₀ copies input
  let qAddr := channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v capFine
  have hx : copyInput (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
      copies s.stride bank = x := by funext i k; apply bits_right
  rw [public_ties_iff (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v, hx]
  let bound (i : Fin copies) := ∀ j : Fin (incoming G v), bank (i.val*s.stride+capFine+j.val) = x i j
  have row (i : Fin copies) (t : bound i) :
      (∀ f ∈ W capFine, (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔
      HeadChecks s (fun j => bank (i.val*s.stride+j)) (fine₀ copies input i) (x i) ∧ pad (x i) := by
    simp only [wiring,List.forall_mem_append]
    rw [← List.all_eq_true, fineTies_pass,← List.all_eq_true, fineZeros_pass,← List.all_eq_true]
    have p := GridPadding.factors_pass pack v qAddr
      (fun q k => x i (sourceOrder G channelID groupID v (.inl ⟨q,k⟩))) bank (i.val*s.stride) i.val
      (fun l => by simpa only [qAddr,channelAddress,Nat.add_assoc] using t (sourceOrder G channelID groupID v (.inl ⟨l.1,l.2⟩)))
    rw [p]
    constructor
    · rintro ⟨⟨ft,fz⟩,pd⟩
      refine ⟨⟨fun j => (ft j).trans ?_,fz,fun j => ?_⟩,pd⟩
      · simpa only [scalarFine,Nat.add_assoc] using t (idx j)
      · simpa only [sc,Nat.add_assoc] using t j
    · rintro ⟨⟨ft,fz,_⟩,pd⟩
      refine ⟨⟨fun j => (ft j).trans ?_,fz⟩,pd⟩
      simpa only [scalarFine,Nat.add_assoc] using (t (idx j)).symm
  constructor
  · rintro ⟨hp,hw⟩
    exact ⟨fun i => ((row i (hp i)).mp (hw i)).1,fun i => ((row i (hp i)).mp (hw i)).2⟩
  · rintro ⟨hs,hp⟩
    have hb (i : Fin copies) : bound i := by
      intro j
      simpa only [sc,Nat.add_assoc] using (hs i).2.2 j
    exact ⟨hb,fun i => (row i (hb i)).mpr ⟨hs i,hp i⟩⟩

/-- Ordinary gate checks in a single copy on its original fine wire bank.
The weighted unary locations have already determined their private report. -/
noncomputable def finePass (g : Fin (guessedSize N cell v) → Bool) (u : Fin (suppliedSize N cell v) → Bool) : Prop :=
  ∀ w, (rules w).base (fun l => copyBits N cell v g u (GridBoxes.lane N cell v edgeID portID w l)) = true


/-- Each weighted vertex's actual selected bit, read on the same fine hidden
wire assignment used by every ordinary Boolean guard. -/
noncomputable def selectedUses (g : Fin (guessedSize N cell v) → Bool) (u : Fin (suppliedSize N cell v) → Bool)
    (j : Fin (count fs)) : Bool :=
  copyBits N cell v g u (selectedWire N cell v siteID edgeID portID rules j)

local notation "select₀" => selectedUses N cell siteID edgeID portID v rules
local notation "pass₀" => finePass N cell edgeID portID v rules

/-- The unsupplemented native birth site already forces every real report bit
and every padding bit. Its only independent choices are the original fine
wire guesses passing the ordinary Boolean guards. -/
theorem weighted_acceptance (copies capFine capReport : ℕ)
    (hf : GridBoxes.stride N cell v ≤ capFine) (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool)
    (work : Fin (copies*(s₀ capFine capReport hf hc).stride) → Bool) :
    let s := s₀ capFine capReport hf hc
    let u := fine₀ copies input
    let x := slice₀ copies input
    let uses := fun (g : Fin copies → Fin s.guessed → Bool) (i : Fin copies) => select₀ (g i) (u i)
    ((birth copies capFine capReport).observe (bits work input)).isSome = true ↔
      s.DynamicChecks copies u x uses work ∧ (∀ i, pad (x i)) ∧
        ∀ i, pass₀ (s.decodeWork copies work i) (u i) := by
  intro s u x uses
  let bank := bits work input
  let g := s.decodeWork copies work
  let box := box₀ capFine capReport
  let row (f : Factor) (i : Fin copies) := (f.observe bank (i.val*s.stride) i.val).isSome = true
  let ties := ∀ r ∈ BottomRepeat.ties G channelID groupID v copies capFine s.stride, r.Valid [box] bank
  let wire := ∀ (i : Fin copies) f, f ∈ W capFine → row f i
  let staged (i : Fin copies) := ∀ f ∈ stage s.orig fs, row f i
  let zero (i : Fin copies) := ∀ f ∈ reportZeros s.orig s.used capReport, row f i
  have actual : ((birth copies capFine capReport).observe bank).isSome = true ↔
      (ties ∧ wire) ∧ ∀ i, staged i ∧ zero i := by
    have h := BottomRepeat.bornWith_accepts G channelID groupID v copies capFine s.stride box bank
    apply h.trans
    have hmem (i : Fin copies) : (∀ f ∈ box, row f i) ↔
        (staged i ∧ ∀ f ∈ W capFine, row f i) ∧ zero i := by
      simp only [box,stored,List.forall_mem_append]
      rfl
    constructor
    · rintro ⟨ht,hb⟩
      have h₁ (i : Fin copies) := (hmem i).mp (hb i i.isLt)
      exact ⟨⟨ht,fun i => (h₁ i).1.2⟩,fun i => ⟨(h₁ i).1.1,(h₁ i).2⟩⟩
    · rintro ⟨⟨ht,hw⟩,hrest⟩
      exact ⟨ht,fun i hi => (hmem ⟨i,hi⟩).mpr ⟨⟨(hrest ⟨i,hi⟩).1,hw ⟨i,hi⟩⟩,(hrest ⟨i,hi⟩).2⟩⟩
  have hh := heads N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
    copies capFine capReport hf hc input work [box]
  have selected (i : Fin copies) (head : HeadChecks s (fun j => bank (i.val*s.stride+j)) (u i) (x i)) :
      staged i ↔ pass₀ (g i) (u i) ∧
        ∀ j : Fin s.used, bank (i.val*s.stride+(s.orig+j.val)) = uses g i j := by
    have fineRead (k : Fin (GridBoxes.stride N cell v)) :
        bank (i.val*s.stride+k.val) = copyBits N cell v (g i) (u i) k :=
      s.readFine copies work input i (u i) head.1 k
    have h := stage_pass bank (i.val*s.stride) i.val s.orig fs
    refine h.trans (and_congr ?_ ?_)
    · refine (ordinary_grid N cell v siteID edgeID portID rules bank (i.val*s.stride) i.val).trans ?_
      simp only [finePass,fineRead]
    · apply forall_congr'
      intro j
      have w := fineRead (selectedWire N cell v siteID edgeID portID rules j)
      change (bank (i.val*s.stride+s.orig+j.val) = bank (i.val*s.stride+(selectedWire N cell v siteID edgeID portID rules j).val)) ↔ _
      rw [Nat.add_assoc,w]
      rfl
  have ziff (i : Fin copies) : zero i ↔ ∀ j < s.capReport-s.used,
      bank (i.val*s.stride+(s.orig+s.used+j)) = false := by
    change (∀ f ∈ reportZeros s.orig s.used s.capReport, (f.observe bank (i.val*s.stride) i.val).isSome = true) ↔ _
    rw [← List.all_eq_true,reportZeros_pass]
  have chk := s.workChecks_bits copies u x work input (uses g)
  constructor
  · intro ha
    obtain ⟨wiring,hrows⟩ := actual.mp ha
    obtain ⟨head,hpad⟩ := hh.mp wiring
    have sel (i : Fin copies) := (selected i (head i)).mp (hrows i).1
    refine ⟨chk.mpr ?_,hpad,fun i => (sel i).1⟩
    intro i
    exact ⟨(head i).1,(head i).2.1,(head i).2.2,(sel i).2,(ziff i).mp (hrows i).2⟩
  · rintro ⟨good,hpad,passing⟩
    have ok := chk.mp good
    have head (i : Fin copies) : HeadChecks s (fun j => bank (i.val*s.stride+j)) (u i) (x i) :=
      ⟨(ok i).1,(ok i).2.1,(ok i).2.2.1⟩
    exact actual.mpr ⟨hh.mpr ⟨head,hpad⟩,fun i =>
      ⟨(selected i (head i)).mpr ⟨passing i,(ok i).2.2.2.1⟩,(ziff i).mpr (ok i).2.2.2.2⟩⟩


private theorem mapM_constant {α β : Type*} (xs : List α) (f : α → Option β) (b : β)
    (h : ∀ x ∈ xs, f x = some b) : xs.mapM f = some (List.replicate xs.length b) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨ha,ht⟩ := List.forall_mem_cons.mp h
    simp only [List.mapM_cons,ha,ih ht,Option.pure_def,Option.bind_eq_bind,Option.bind_some,
      List.length_cons,List.replicate_succ]

/-- All observations of a passing original box are the same positive untagged
read, one for each of its real private factor occurrences. -/
theorem weighted_observations (copies capFine capReport : ℕ) (bank : ℕ → Bool)
    (passing : ((birth copies capFine capReport).observe bank).isSome = true) :
    (birth copies capFine capReport).observe bank =
      some (List.replicate (copies*(box₀ capFine capReport).length) (false,none)) := by
  let sz := bottomStride (capFine+incoming G v) capReport
  let box := box₀ capFine capReport
  let state := BottomRepeat.bornWith G channelID groupID v copies capFine sz box
  change state.observe bank = _
  obtain ⟨ht,hf⟩ := (BottomRepeat.bornWith_accepts G channelID groupID v copies capFine sz box bank).mp passing
  rw [Site.observe,ite_eq_left ((BottomRepeat.bornWith_rows_valid G channelID groupID v copies capFine sz box bank).mpr ht),
    Directory.observations,BottomRepeat.bornWith_occurrences]
  rw [mapM_constant _ _ (false,none)]
  · simp [List.length_flatMap,box]
  · intro o ho
    obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp ho
    obtain ⟨f,hmem,rfl⟩ := List.mem_map.mp hm
    have ok := hf i (List.mem_range.mp hi) f hmem
    obtain ⟨ws,rs,rfl⟩ := stored_truth N cell position pack width owner lane aligned siteID edgeID portID
      channelID groupID v rules capFine capReport f hmem
    change (Factor.truth ws rs).observe bank (i*sz) i = some (false,none)
    unfold Factor.observe at ok ⊢
    split <;> simp_all

/-- The field-valued local table of the unlinked weighted source site sums each
passing tuple of original fine wires once. The report bits are included in the
physical sum and eliminated by their checked bijection. -/
theorem weighted_value {K : Type*} [Field K] (values : ℕ → K) (copies capFine capReport : ℕ)
    (hf : GridBoxes.stride N cell v ≤ capFine) (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)
    (input : Fin (incoming (BottomRepeat.wide G copies) v) → Bool) :
    (birth copies capFine capReport).value (fieldWeight values) input =
      if ∀ i, pad (slice₀ copies input i) then ∑ g : Fin copies → Fin (guessedSize N cell v) → Bool,
        ∏ i : Fin copies, if pass₀ (g i) (fine₀ copies input i) then (1:K) else 0 else 0 := by
  let s := s₀ capFine capReport hf hc
  let u := fine₀ copies input
  let x := slice₀ copies input
  let uses (g : Fin copies → Fin s.guessed → Bool) (i : Fin copies) := select₀ (g i) (u i)
  let valid := s.DynamicChecks copies u x uses
  let pass (g : Fin copies → Fin s.guessed → Bool) := ∀ i, pass₀ (g i) (u i)
  let state := birth copies capFine capReport
  have point (work : Fin (copies*s.stride) → Bool) :
      (state.observe (bits work input)).elim 0 (fieldWeight values) =
        if valid work ∧ (∀ i, pad (x i)) ∧ pass (s.decodeWork copies work) then 1 else 0 := by
    have h := weighted_acceptance N cell position pack width owner lane aligned siteID edgeID portID
      channelID groupID v rules copies capFine capReport hf hc input work
    by_cases p : (state.observe (bits work input)).isSome = true
    · rw [ite_eq_left (h.mp p),weighted_observations N cell position pack width owner lane aligned siteID edgeID portID
        channelID groupID v rules copies capFine capReport (bits work input) p]
      simp [fieldWeight_eq_prod,fieldEntry]
    · rw [ite_eq_right (fun q => p (h.mpr q))]
      cases e : state.observe (bits work input) with
      | none => rfl
      | some => simp [e] at p
  change (∑ work : Fin (copies*s.stride) → Bool, (state.observe (bits work input)).elim 0 (fieldWeight values)) = _
  simp_rw [point]
  by_cases hp : ∀ i, pad (x i)
  · rw [ite_eq_left hp]
    let read (work : Fin (copies*s.stride) → Bool) : K := if pass (s.decodeWork copies work) then 1 else 0
    have sep (work : Fin (copies*s.stride) → Bool) :
        (if valid work ∧ (∀ i, pad (x i)) ∧ pass (s.decodeWork copies work) then (1:K) else 0) =
        if valid work then read work else 0 := by by_cases hh : valid work <;> simp [hh,hp,read]
    simp_rw [sep]
    rw [← Finset.sum_filter,Finset.sum_subtype (p := valid) _ (fun _ => by simp) read]
    rw [← (s.dynamicGuessEquiv copies u x uses).sum_comp (fun w => read w.val)]
    apply Finset.sum_congr rfl
    intro g _
    change (if pass (s.decodeWork copies ((s.checkedGuessEquiv copies u x (uses g) g).val)) then (1:K) else 0) = _
    refine (congrArg (fun y => if pass y then (1:K) else 0) (s.decode_checked copies u x (uses g) g)).trans ?_
    rw [Fintype.prod_boole]
    by_cases hg : pass g <;> simp only [pass,u] at hg ⊢ <;> simp [hg]
  · rw [ite_eq_right hp]
    simp [hp]

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
