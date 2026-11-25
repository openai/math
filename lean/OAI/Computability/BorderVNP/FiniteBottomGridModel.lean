import OAI.Computability.BorderVNP.FiniteBottomGridFactors
import OAI.Computability.BorderVNP.FiniteBottomGridTables
import OAI.Computability.BorderVNP.PackedBottomScalarValue

/-! # Concrete finite-field bottom cells model the grouped physical grid

The initial immutable scalar directory represents the contraction of the
actual fine tables, including every original hidden wire and every field
element. Copies use independent hidden wire choices. Channel padding and
the selected external group lanes are taken from the public wide network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing CellAddresses Inherited BottomGridBank
open scoped BigOperators Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable {F : Type*} [Field F] [Fintype F]

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "grid" => Network.uniformGrid (Network.cellNetwork N cell position) src dst H
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "pad" => publicPad N cell position pack width owner channelID groupID v
local notation "slab₀" => scalarSlab (src := src) (dst := dst) (H := H) N cell position width owner v
local notation "slice₀" => scalarSlice (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
local notation "fine₀" => scalarFine N cell position pack width owner lane aligned edgeID portID channelID groupID v
local notation "fs" => scalarFactors N cell v siteID edgeID portID
local notation "W" => wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v

/-- The actual immutable bottom site with one scalar gadget factor per fine
site, followed by its fine ties and both physical padding checks. -/
noncomputable def finiteBorn (T : N.Tables F) (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine) :
    Site :=
  BottomRepeat.bornWith G channelID groupID v copies capFine (slab₀ capFine fit).stride (fs T ++ W capFine)

local notation "birth" => finiteBorn N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v

omit [Fintype P] in
private theorem slice_words (copies : ℕ) (z : Incident (BottomRepeat.wide G copies) v → Fin (copies*H) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G copies) v, Fin (copies*width p.val) → Bool) (i : Fin copies) :
    slice₀ copies (inputWords (BottomRepeat.wide G copies) channelID groupID v z x) i =
      inputWords G channelID groupID v (fun e k => z e (finProdFinEquiv (i,k))) (fun p k => x p (finProdFinEquiv (i,k))) := by
  funext k
  obtain ⟨u,rfl⟩ := (sourceOrder G channelID groupID v).surjective k
  rcases u with ⟨e,k⟩ | ⟨p,k⟩ <;>
    simp only [scalarSlice,Equiv.symm_apply_apply,BottomRepeat.repeatInput,inputWords_wire,inputWords_port]

/-- The true repeated packed grid table, with the copies sharing each
physical incidence word and the original fine bits occupying their named group slots. -/
noncomputable abbrev repeatedTable (T : N.Tables F) (copies : ℕ) : (BottomRepeat.wide G copies).Tables F :=
  ((grid).repeatGrid copies).externalTables _ (Network.repeatLane width lane copies) owner
    (fun p => aligned p.2) ((grid).repeatTables copies (pack.tables (N.cellTables cell position T)))

local notation "table₀" => repeatedTable N cell position pack width owner lane aligned

/-- A field dictionary can contain other gadget values as long as its
allocated fine scalar codes denote the original elements. -/
theorem finiteBorn_models_of_dictionary (T : N.Tables F) (copies capFine : ℕ)
    (fit : GridBoxes.stride N cell v ≤ capFine) (values : ℕ → F)
    (lookup : ∀ a : F, values (Fintype.equivFin F a).val = a) :
    (birth T copies capFine fit).Models (BottomRepeat.wide G copies) channelID groupID v rfl
      (fieldWeight values) (table₀ T copies) := by
  intro z x
  let input := inputWords (BottomRepeat.wide G copies) channelID groupID v z x
  let t (i : Fin copies) := (grid).externalTables width lane owner aligned (pack.tables (N.cellTables cell position T))
    v (fun e k => z e (finProdFinEquiv (i,k))) (fun p k => x p (finProdFinEquiv (i,k)))
  let s := slab₀ capFine fit
  let u := fine₀ copies input
  let b (g : Fin copies → Fin (guessedSize N cell v) → Bool) := bits
    (scalarWork N cell position pack width owner lane aligned edgeID portID channelID groupID v copies capFine fit input g) input
  have hw : fieldWeight values = fun os => (os.map (fieldEntry values)).prod := funext (fieldWeight_eq_prod values)
  have hs := scalarBox_value N cell position pack width owner lane aligned edgeID portID channelID groupID v
    copies capFine fit (fs T) (fieldEntry values) (by simp [fieldEntry]) input
  have factor_eq (g : Fin copies → Fin (guessedSize N cell v) → Bool) (i : Fin copies) :
      BottomRepeat.boxProduct (fieldEntry values) (fs T) (b g) s.stride i.val =
        factor N cell v edgeID portID T (g i) (u i) :=
    scalarFactors_product N cell v siteID edgeID portID T (b g) (i.val*s.stride) i.val (g i) (u i)
      (scalarWork_fine N cell position pack width owner lane aligned edgeID portID channelID groupID v copies capFine fit input g i)
      values lookup
  have hc (i : Fin copies) : (if pad (slice₀ copies input i) then
      ∑ g, factor N cell v edgeID portID T g (u i) else 0) = t i := by
    change (if pad (slice₀ copies input i) then ∑ g, factor N cell v edgeID portID T g
      (fun k => slice₀ copies input i (fineIndex k)) else 0) = t i
    simp only [input,slice_words,t]
    exact oneCopy_entry N cell position pack width owner lane aligned edgeID portID channelID groupID v T _ _
  change (birth T copies capFine fit).value (fieldWeight values) input = _
  rw [hw]
  refine hs.trans (Eq.trans ?_ (repeated_entry N cell position pack width owner lane aligned v copies T z x))
  change (if ∀ i, pad (slice₀ copies input i) then
    ∑ g, ∏ c : Fin copies, BottomRepeat.boxProduct (fieldEntry values) (fs T) (b g) s.stride c.val else 0) = ∏ i, t i
  simp only [factor_eq]
  by_cases hp : ∀ i, pad (slice₀ copies input i)
  · rw [ite_eq_left hp,← Fintype.prod_sum (fun (i : Fin copies) g => factor N cell v edgeID portID T g (u i))]
    exact Finset.prod_congr rfl fun i _ => (ite_eq_left (hp i)).symm.trans (hc i)
  · rw [ite_eq_right hp]
    obtain ⟨i,hi⟩ := not_forall.mp hp
    exact (Finset.prod_eq_zero (Finset.mem_univ i) ((hc i).symm.trans (ite_eq_right hi))).symm

/-- Every concrete finite-field bottom site realizes its actual grid table
under the canonical finite scalar dictionary. -/
theorem finiteBorn_models (T : N.Tables F) (copies capFine : ℕ) (fit : GridBoxes.stride N cell v ≤ capFine) :
    (birth T copies capFine fit).Models (BottomRepeat.wide G copies) channelID groupID v rfl
      (fieldWeight (scalarValue F)) (table₀ T copies) :=
  finiteBorn_models_of_dictionary N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
    v T copies capFine fit (scalarValue F) scalarValue_code

end Packing.FiniteBottom

end BorderVNP
end Computability
end OAI
