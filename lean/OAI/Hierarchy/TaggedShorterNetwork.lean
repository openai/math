import OAI.Hierarchy.TaggedShorterBank
import OAI.Hierarchy.TaggedShorterLinks
import OAI.Hierarchy.TaggedShorterPairIdle

namespace OAI
/-! # Physical positive-scale link networks

The two checked compaction stages transport identifiers along with payloads.
Each physical module has two equal-format tagged calls sharing all tag bits.
The first compares identifiers and ordered blank ranks, the second checks the
original link payloads. The single exposed hole contains all calls of this type.
-/

noncomputable section
namespace Hierarchy.TaggedShorterNetwork
open ThreeFlat Routing Spill
open TaggedShorterCompaction
open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {D S M n d w : ℕ}

abbrev Local (n d w : ℕ) := Pair (2^n) (d+w)
abbrev Hole := TaggedShorterPair.Hole

private def localWire (n d w : ℕ) : TaggedShorterPair.Pin n d w → Option (Local n d w) ⊕ Hole n w
  | .inl (.inl (b,i,none)) => .inl (some (b,i,none))
  | .inl (.inl (b,i,some j)) => .inl (some (b,i,some (Fin.castAdd w j)))
  | .inl (.inr (b,i,j)) => .inl (some (b,i,some (Fin.natAdd d j)))
  | .inr h => .inr h

def lane (F : Type*) [CommSemiring F] (n d w : ℕ) :
    BitNetwork F (Fintype.card (Option (Local n d w) ⊕ Hole n w)) :=
  TypedWiring.glue (fun _ : Unit => TaggedShorterPair.installedCut F n d w)
    (fun _ p => (Sum.inl (p.elim (.inl none) (localWire n d w)) : _ ⊕ Empty))

@[simp] theorem lane_cells : (lane F n d w).cells = (TaggedShorterPair.installedCut F n d w).cells := by simp [lane]

def oracle (F : Type*) [CommSemiring F] (n w : ℕ) (z : Hole n w → Bool) :=
  Tagged.coeff F n w (fun j => z (false,j)) * Tagged.coeff F n w (fun j => z (true,j))

private def header {A : Type*} (ids : A ↪ Tagged.Bits d) (data : A → Tagged.Bits w) :
    A ↪ Tagged.Bits (d+w) where
  toFun a := Fin.append (ids a) (data a)
  inj' := by
    intro a b eq
    apply ids.injective
    funext j
    simpa using congrFun eq (Fin.castAdd w j)

/-- A pair of compacted lists can be in different physical orders. Their
identifiers select the same labelled occurrences on both sides. -/
theorem lane_checks (metadataRoom : 1+d+n ≤ w) {A : Type*} [Fintype A]
    (ids : A ↪ Tagged.Bits d) (data : Bool → A → Tagged.Bits w)
    (y : Option (Local n d w) → Bool)
    (mass : ∀ s, payloads (fun p => y (some (s,p))) = Finset.univ.val.map (header ids (data s)))
    (blanks : ∀ s, ZeroBlanks (fun p => y (some (s,p)))) :
    TaggedShorterBank.closeLane (lane F n d w) (oracle F n w) y =
      if y none then (if ∀ a, data true a = data false a then 1 else 0) else 1 := by
  let id s i j := y (some (s,i,some (Fin.castAdd w j)))
  let value s i j := y (some (s,i,some (Fin.natAdd d j)))
  choose pos occ words using fun s =>
    TaggedShorterLinks.positions (header ids (data s)) (fun p => y (some (s,p))) (mass s)
  have flags s i : y (some (s,i,none)) = decide (i ∈ Set.range (pos s)) := by
    apply Bool.eq_iff_iff.mpr
    simpa using occ s i
  have hId s a : id s (pos s a) = ids a := by
    funext j
    exact (words s a (Fin.castAdd w j)).trans (Fin.append_left (ids a) (data s a) j)
  have hValue s a : value s (pos s a) = data s a := by
    funext j
    exact (words s a (Fin.natAdd d j)).trans (Fin.append_right (ids a) (data s a) j)
  have vacant s i (hi : i ∉ Set.range (pos s)) : value s i = fun _ => false := by
    funext j
    exact blanks s i (by simp [flags,hi]) _
  let combined := TaggedShorterPair.inputs (fun s i => decide (i ∈ Set.range (pos s))) id value
  have localEval (z : Hole n w → Bool) :
      TypedWiring.value (lane F n d w) (Sum.elim y z) =
        TypedWiring.value (TaggedShorterPair.installedCut F n d w)
          (fun p => p.elim (y none) (Sum.elim combined z)) := by
    rw [lane,TypedWiring.glue_value,Fintype.sum_unique,Fintype.prod_unique]
    apply congrArg (TypedWiring.value (TaggedShorterPair.installedCut F n d w))
    funext p
    rcases p with _ | (((⟨s,i,_ | j⟩ | ⟨s,i,j⟩)) | h)
    · rfl
    · exact flags s i
    all_goals rfl
  unfold TaggedShorterBank.closeLane
  simp_rw [localEval]
  have exactLane := TaggedShorterPair.installedCut_contract F (y none) metadataRoom ids pos id hId value vacant
  simp only [combined,hValue,oracle] at exactLane ⊢
  refine Eq.trans (Finset.sum_congr ?_ (fun _ _=>rfl)) exactLane
  ext z
  simp

theorem idle (metadataRoom : 1+d+n ≤ w) :
    TaggedShorterBank.closeLane (lane F n d w) (oracle F n w) (fun _ => false) = 1 := by
  let ids : Empty ↪ Tagged.Bits d := ⟨Empty.elim,fun a => Empty.elim a⟩
  have zero := lane_checks (F:=F) metadataRoom ids (fun _ => Empty.elim) (fun _ => false)
    (fun _ => by simp [payloads,occupied]) (fun _ _ _ _ => rfl)
  simpa using zero

/-- Physical readout is fixed at every source and target position. The control
pins select occupied positions, attach the common occurrence identifier, and
mark the nonempty batches. The payload itself is read from a public address. -/
def input {P : Type*} (read : Fin S × Bool → Fin D → P) (data : P → Tagged.Bits w)
    (pool : Fin S → Bool) (mask : Fin S × Bool → Fin D → Bool)
    (id : Fin S × Bool → Fin D → Tagged.Bits d) : Input S D (d+w) → Bool
  | .inl s => pool s
  | .inr (s,b,i,none) => mask (s,b) i
  | .inr (s,b,i,some j) => Fin.append (id (s,b) i) (data (read (s,b) i)) j

/-- For every legal occupancy and unit labelling, the same public board
checks the payloads at the prescribed endpoints. The paths in both
compactors and the completed tags are internal. -/
theorem checks
    (near : Compactor F D (2^n) (d+w)) (far : Compactor F S M (Width (2^n) (d+w)))
    (metadataRoom : 1+d+n ≤ w) {P : Type*} (read : Fin S × Bool → Fin D → P)
    (data : P → Tagged.Bits w) {U : Fin S → Type*} [∀ s, Fintype (U s)]
    (place : ∀ s, Bool → U s ↪ Fin D)
    (ids : ∀ s, U s ↪ Tagged.Bits d) (id : Fin S × Bool → Fin D → Tagged.Bits d)
    (bindId : ∀ s b a, id (s,b) (place s b a) = ids s a)
    (localFit : ∀ s, 2*Fintype.card (U s) ≤ 2^n)
    (poolFit : 2*(Finset.univ.filter (fun s => Nonempty (U s))).card ≤ M) :
    let x := input read data (fun s => decide (Nonempty (U s)))
      (fun sb i => decide (i ∈ Set.range (place sb.1 sb.2))) id
    TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n d w))
      (oracle F n w) x =
      if ∀ s a, data (read (s,true) (place s true a)) = data (read (s,false) (place s false a))
      then 1 else 0 := by
  intro x
  let value s b a := data (read (s,b) (place s b a))
  have occ s b : occupied (row x s b) = Finset.univ.map (place s b) := by
    ext i; simp [occupied,row,x,input,Set.mem_range]
  have mass s b : payloads (row x s b) = Finset.univ.val.map (header (ids s) (value s b)) := by
    unfold payloads
    rw [occ]
    change (Finset.univ.val.map (place s b)).map _ = _
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    change Fin.append (id (s,b) (place s b a)) (value s b a) = _
    rw [bindId]; rfl
  have fits s b : 2*(occupied (row x s b)).card ≤ 2^n := by
    simpa only [occ,Finset.card_map,Finset.card_univ] using localFit s
  obtain ⟨y,z,localData,pairs,blanks,hits⟩ := routes near far x fits (by simpa [x,input] using poolFit)
  rw [TaggedShorterBank.close_eq near far _ x z hits,TaggedShorterBank.physical_product x y z pairs blanks _ (idle metadataRoom)]
  have candidate (s : Fin S) : TaggedShorterBank.closeLane (lane F n d w) (oracle F n w)
      (fun p => p.elim true (fun t => y (s,t))) = if ∀ a, value s true a = value s false a then 1 else 0 := by
    change _ = if true then (if ∀ a, value s true a = value s false a then 1 else 0) else 1
    apply lane_checks metadataRoom (ids s) (value s)
    · intro b; exact (localData s b).1.trans (mass s b)
    · intro b; exact (localData s b).2
  simp_rw [candidate]
  have each (s : Fin S) :
      (if x (.inl s) = true then (if ∀ a, value s true a = value s false a then (1:F) else 0) else 1) =
        if ∀ a, value s true a = value s false a then 1 else 0 := by
    by_cases hn : Nonempty (U s)
    · simp [x,input,hn]
    · have : IsEmpty (U s) := not_nonempty_iff.mp hn
      simp
  simp_rw [each]
  have test := Fintype.prod_boole (M₀:=F) (p:=fun s : Fin S => ∀ a : U s,value s true a=value s false a)
  apply test.trans
  by_cases good : ∀ (s : Fin S) (a : U s),value s true a=value s false a
  · exact (ite_eq_left good).trans (ite_eq_left good).symm
  · exact (ite_eq_right good).trans (ite_eq_right good).symm

end Hierarchy.TaggedShorterNetwork

end
end OAI
