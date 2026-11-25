import OAI.Computability.BorderVNP.DiagonalExternalTileFree

/-! # A bounded list of physical source intervals for one retained team tile

Each directed cable end is a positive affine range. The literal and pin lanes
form one free range, and the tail beyond the processor array is a zero range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.TileRuns

open scoped Classical
variable {R r w link g : ℕ}

/-- Which source is used throughout one run in the original site word. -/
inductive Kind (R r w link g : ℕ)
  | zero
  | free
  | cable (side : Bool) (piece : Cables R r w link g)

/-- The genuine fine physical slot read at within-run offset `i`. Free slots use the old tile lane unchanged. -/
def Reads (u : Fin (R+1)) (tile : ℕ) (kind : Kind R r w link g) (i : ℕ) (k : Fin g) : Prop :=
  match kind with
  | .zero => lookup (r := r) (w := w) (link := link) u tile k = none
  | .free => ∃ f : FreePort R r w, lookup (link := link) u tile k = some (.inl f)
  | .cable side piece => ∃ j : Fin (cableWidth piece), j.val = i ∧
      lookup u tile k = some (.inr (side,⟨piece,j⟩))

/-- One affine or zero-clamped interval on a particular tile of the old input. -/
structure Run (R r w link g : ℕ) (u : Fin (R+1)) (tile : ℕ) where
  /-- First lane in the original grouped tile. -/
  first : ℕ
  /-- Number of consecutive original input lanes. -/
  width : ℕ
  /-- Physical source of this consecutive range. -/
  kind : Kind R r w link g
  /-- The exclusive end of the interval fits the original tile. -/
  fit : first+width ≤ g
  /-- Exact fine slot at every lane of the interval. -/
  read : ∀ i < width, ∀ k : Fin g, k.val = first+i → Reads u tile kind i k

local notation "stride" => 2*w+R*link
variable (u : Fin (R+1)) (tile : ℕ)

private theorem cable_block (hg : 0 < g) (s : Bool) (c : Cables R r w link g) (j : Fin (cableWidth c))
    (hc : fieldBlock w stride link g c s = (u,tile)) :
    fieldTeam c.1.1 s = u ∧ tile*g ≤ cableStart s c+j.val ∧ cableStart s c+j.val < tile*g+g := by
  rw [fieldBlock_bit w stride link g c s j] at hc
  obtain ⟨ht,hb⟩ := Prod.mk.inj hc
  obtain ⟨hl,hr⟩ := (Nat.div_eq_iff hg).mp hb
  have he := pieceOffset_eq_start_add _ _ hg c j
  rw [he] at hl hr
  dsimp only [cableStart]
  exact ⟨ht,by omega,by omega⟩

private noncomputable def cableRun (hg : 0 < g) (s : Bool) (c : Cables R r w link g)
    (hc : fieldBlock w stride link g c s = (u,tile)) : Run R r w link g u tile := by
  have pos : 0 < cableWidth c := pieceWidth_pos _ _ c
  let last : Fin (cableWidth c) := ⟨cableWidth c-1,by omega⟩
  have team := (cable_block u tile hg s c ⟨0,pos⟩ hc).1
  have first := (cable_block u tile hg s c ⟨0,pos⟩ hc).2.1
  have endFit := (cable_block u tile hg s c last hc).2.2
  simp only [Nat.add_zero] at first
  change cableStart s c+(cableWidth c-1) < tile*g+g at endFit
  refine ⟨cableStart s c-tile*g,cableWidth c,.cable s c,by omega,?_⟩
  intro i hi k hk
  refine ⟨⟨i,hi⟩,rfl,(lookup_some ..).mpr ⟨(cable_team s c _).trans team,?_⟩⟩
  rw [cable_ordinal hg]
  dsimp only
  omega

private noncomputable def freeSet : Finset (Fin g) :=
  Finset.univ.filter (fun j => ∃ f : FreePort R r w, lookup (link := link) u tile j = some (.inl f))

private theorem free_mem (j : Fin g) :
    j ∈ freeSet (r := r) (w := w) (link := link) u tile ↔
      ∃ f : FreePort R r w, lookup (link := link) u tile j = some (.inl f) := by simp [freeSet]

private noncomputable def freeRun (small : g ≤ link) : Run R r w link g u tile := by
  let S := freeSet (r := r) (w := w) (link := link) (g := g) u tile
  by_cases pos : S.Nonempty
  · let lo := S.min' pos
    let hi := S.max' pos
    have sorted : lo.val ≤ hi.val := S.min'_le_max' pos
    have bound := hi.isLt
    refine ⟨lo.val,hi.val+1-lo.val,.free,by omega,?_⟩
    intro i fit k eqn
    obtain ⟨a,ha⟩ := (free_mem u tile lo).mp (S.min'_mem pos)
    obtain ⟨b,hb⟩ := (free_mem u tile hi).mp (S.max'_mem pos)
    exact free_between small u tile (show lo.val ≤ k.val by omega) (show k.val ≤ hi.val by omega) a b ha hb
  · exact ⟨0,0,.free,by omega,fun i hi => (Nat.not_lt_zero i hi).elim⟩

private theorem freeRun_covers (small : g ≤ link) (k : Fin g) (f : FreePort R r w)
    (h : lookup (link := link) u tile k = some (.inl f)) :
    let q := freeRun (r := r) (w := w) u tile small
    ∃ i < q.width, k.val = q.first+i := by
  let S := freeSet (r := r) (w := w) (link := link) (g := g) u tile
  have hm : k ∈ S := (free_mem u tile _).mpr ⟨f,h⟩
  have pos : S.Nonempty := ⟨k,hm⟩
  have lo : (S.min' pos).val ≤ k.val := S.min'_le k hm
  have hi : k.val ≤ (S.max' pos).val := S.le_max' k hm
  dsimp only [S] at pos lo hi
  simp only [freeRun,dite_eq_left pos]
  exact ⟨k.val-(S.min' pos).val,by dsimp only [S]; omega,by dsimp only [S]; omega⟩

private def zeroRun : Run R r w link g u tile := by
  let a := min g (r*stride-tile*g)
  have fit : a ≤ g := min_le_left ..
  refine ⟨a,g-a,.zero,by omega,?_⟩
  intro i hi k hk
  apply (lookup_none ..).mpr
  dsimp only [a] at *
  omega

private def ends := Finset.univ.filter fun x : Bool × Cables R r w link g => fieldBlock w stride link g x.2 x.1 = (u,tile)

/-- At most six intervals cover the whole initial tile, including a partially occupied last block. -/
noncomputable def runs (hg : 0 < g) (small : g ≤ link) : List (Run R r w link g u tile) :=
  let S := ends (r := r) (w := w) (link := link) (g := g) u tile
  zeroRun u tile :: freeRun u tile small :: S.attach.toList.map fun x =>
    cableRun u tile hg x.val.1 x.val.2 (by simpa only [S,ends,Finset.mem_filter,Finset.mem_univ,true_and] using x.property)

/-- At most four of the tile's six physical intervals are cable ends. -/
theorem runs_length (hg : 0 < g) (small : g ≤ link) :
    (runs (r := r) (w := w) u tile hg small).length ≤ 6 := by
  have bound := physical_ends_per_block (r := r) w stride link g (by omega) hg small u tile
  simp only [runs,List.length_cons,List.length_map,Finset.length_toList,Finset.card_attach]
  exact Nat.add_le_add_right (Nat.add_le_add_right bound 1) 1

/-- Every old tile lane belongs to a listed interval whose recorded source is its actual sewn input. -/
theorem runs_cover (hg : 0 < g) (small : g ≤ link) (k : Fin g) :
    ∃ q ∈ runs (r := r) (w := w) u tile hg small, ∃ i < q.width, k.val = q.first+i := by
  cases H : lookup (r := r) (w := w) (link := link) u tile k with
  | none =>
    have hn := (lookup_none ..).mp H
    refine ⟨zeroRun u tile,by simp [runs],k.val-(zeroRun (r := r) (w := w) (link := link) (g := g) u tile).first,?_,?_⟩
    all_goals dsimp only [zeroRun]; have := k.isLt; omega
  | some x =>
    rcases x with f | ⟨s,c,j⟩
    · exact ⟨freeRun u tile small,by simp [runs],freeRun_covers u tile small k f H⟩
    have hc := lookup_fieldBlock u tile k s c j H
    have member : (s,c) ∈ ends (r := r) (w := w) (link := link) (g := g) u tile := by simp [ends,hc]
    let x : ↥(ends (r := r) (w := w) (link := link) (g := g) u tile) := ⟨(s,c),member⟩
    refine ⟨cableRun u tile hg s c hc,?_,j.val,j.isLt,?_⟩
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨x,by simp,rfl⟩
    · obtain ⟨_,hj⟩ := (lookup_some ..).mp H
      rw [cable_ordinal hg] at hj
      have first := (cable_block u tile hg s c ⟨0,pieceWidth_pos _ _ c⟩ hc).2.1
      change k.val = (cableStart s c-tile*g)+j.val
      simp only [Nat.add_zero] at first
      omega

/-- Each source kind occurs once, including the individual directed cable ends. -/
theorem runs_nodup_kind (hg : 0 < g) (small : g ≤ link) :
    ((runs (r := r) (w := w) u tile hg small).map Run.kind).Nodup := by
  let S := ends (r := r) (w := w) (link := link) (g := g) u tile
  let mark (x : ↥S) := Kind.cable (R := R) (r := r) (w := w) (link := link) (g := g) x.val.1 x.val.2
  have free : (freeRun (r := r) (w := w) u tile small).kind = .free := by
    by_cases h : (freeSet (r := r) (w := w) (link := link) (g := g) u tile).Nonempty <;> simp [freeRun,h]
  have eq : (runs (r := r) (w := w) u tile hg small).map Run.kind = .zero :: .free :: S.attach.toList.map mark := by
    simp only [runs,List.map_cons,List.map_map,free]
    rfl
  rw [eq,List.nodup_cons,List.nodup_cons]
  have inject : Function.Injective mark := by
    intro a b he
    obtain ⟨hs,hc⟩ := Kind.cable.inj he
    exact Subtype.ext (Prod.ext hs hc)
  refine ⟨?_,?_,S.attach.nodup_toList.map inject⟩ <;> simp [mark]


end Diagonal.ExternalSew.TileRuns

end BorderVNP
end Computability
end OAI
