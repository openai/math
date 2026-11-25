import OAI.Geometry.Hirsch.Episode
import OAI.Geometry.Hirsch.Tracer

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

structure Program where
  Coord : Type
  [finite : Fintype Coord]
  viable : Set Coord → Prop
  allViable : viable univ
  ancestors : Coord → Set Coord
  self_mem : ∀ idx, idx ∈ ancestors idx

attribute [instance] Program.finite

namespace Program

def closure (prog : Program) (support : Set prog.Coord) : Set prog.Coord :=
  ⋃ idx ∈ support, prog.ancestors idx

theorem subset_closure (prog : Program) (support : Set prog.Coord) : support ⊆ prog.closure support :=
  fun idx hi => mem_iUnion₂.mpr ⟨idx, hi, prog.self_mem idx⟩

def Large (prog : Program) (limit : ℕ) : Prop :=
  ∀ usable, prog.viable usable → limit < usable.ncard

variable {Index : Type} [Fintype Index] (seq : Index → Program)

abbrev join : Program where
  Coord := Σ idx, (seq idx).Coord
  viable usable := ∀ idx, (seq idx).viable (@Sigma.mk _ (fun i => (seq i).Coord) idx ⁻¹' usable)
  allViable idx := (seq idx).allViable
  ancestors idx := @Sigma.mk _ (fun i => (seq i).Coord) idx.1 '' (seq idx.1).ancestors idx.2
  self_mem idx := ⟨idx.2, (seq idx.1).self_mem _, rfl⟩

theorem join_large {limit : ℕ} (idx : Index) (hl : (seq idx).Large limit) :
    (join seq).Large limit := by
  intro usable hv
  apply (hl _ (hv idx)).trans_le
  rw [← ncard_image_of_injective _ (sigma_mk_injective (β := fun i => (seq i).Coord) (i := idx))]
  exact ncard_le_ncard (image_preimage_subset _ _)

theorem join_closure (idx : Index) (support : Set (seq idx).Coord) :
    (join seq).closure (@Sigma.mk _ (fun i => (seq i).Coord) idx '' support) =
      @Sigma.mk _ (fun i => (seq i).Coord) idx '' (seq idx).closure support := by
  ext coord
  simp only [closure, mem_iUnion, mem_image]
  constructor
  · rintro ⟨_, ⟨src, hs, rfl⟩, anc, ha, rfl⟩
    exact ⟨anc, ⟨src, hs, ha⟩, rfl⟩
  · rintro ⟨anc, ⟨src, hs, ha⟩, rfl⟩
    exact ⟨_, ⟨src, hs, rfl⟩, anc, ha, rfl⟩

end Program

structure Package where
  prog : Program
  Row : Type
  [finiteRow : Fintype Row]
  block : Blocking prog.Coord Row

attribute [instance] Package.finiteRow

namespace Package

def size (pkg : Package) := Fintype.card pkg.prog.Coord
def rows (pkg : Package) := Fintype.card pkg.Row
def region (pkg : Package) (limit : ℕ) := pkg.block.admissible pkg.prog.viable limit
def span (pkg : Package) (row : pkg.Row) := (pkg.prog.closure (pkg.block.support row)).ncard

variable {Index : Type} [Fintype Index] (seq : Index → Package)

abbrev Coords := Σ idx, (seq idx).prog.Coord
abbrev Rows := Σ idx, (seq idx).Row

def project (idx : Index) : Vec (Coords seq) →ₗ[ℝ] Vec (seq idx).prog.Coord :=
  LinearMap.funLeft ℝ ℝ (@Sigma.mk _ (fun i => (seq i).prog.Coord) idx)

def projectPoint (idx : Index) : Timed (Coords seq) →ₗ[ℝ] Timed (seq idx).prog.Coord :=
  LinearMap.prodMap LinearMap.id (project seq idx)

def embed (idx : Index) : Vec (seq idx).prog.Coord →ₗ[ℝ] Vec (Coords seq) := by
  classical
  exact LinearMap.pi fun coord => (LinearMap.proj coord.2).comp
    ((LinearMap.proj coord.1).comp (LinearMap.single ℝ (fun i => Vec (seq i).prog.Coord) idx))

omit [Fintype Index] in
theorem project_embed (idx : Index) (dir : Vec (seq idx).prog.Coord) :
    project seq idx (embed seq idx dir) = dir := by
  classical
  ext coord
  simp [project, embed]

omit [Fintype Index] in
theorem project_embed_ne {idx other : Index} (hn : other ≠ idx) (dir : Vec (seq idx).prog.Coord) :
    project seq other (embed seq idx dir) = 0 := by
  classical
  ext coord
  simp [project, embed, hn]

def combined : Blocking (Coords seq) (Rows seq) where
  coeff row := ((seq row.1).block.coeff row.2).comp (project seq row.1)
  slope row := (seq row.1).block.slope row.2
  offset row := (seq row.1).block.offset row.2
  monotone row := fun _ _ hh => (seq row.1).block.monotone row.2 (fun _ => hh _)
  positive row := (seq row.1).block.positive row.2
  individual := by
    rintro ⟨idx, coord⟩
    obtain ⟨row, weight, hw, he⟩ := (seq idx).block.individual coord
    refine ⟨⟨idx, row⟩, weight, hw, ?_⟩
    dsimp only
    rw [he]
    rfl

abbrev join : Package where
  prog := Program.join fun idx => (seq idx).prog
  Row := Rows seq
  block := combined seq

theorem join_size : (join seq).size = ∑ idx, (seq idx).size := Fintype.card_sigma
theorem join_rows : (join seq).rows = ∑ idx, (seq idx).rows := Fintype.card_sigma

omit [Fintype Index] in
theorem support_combined (idx : Index) (row : (seq idx).Row) :
    (combined seq).support ⟨idx, row⟩ =
      @Sigma.mk _ (fun i => (seq i).prog.Coord) idx '' (seq idx).block.support row := by
  classical
  let : DecidableEq (Coords seq) := Classical.typeDecidableEq _
  ext ⟨other, coord⟩
  by_cases he : other = idx
  · subst other
    have hh : project seq idx (Pi.single ⟨idx, coord⟩ 1) = Pi.single coord 1 := by
      ext target
      simp [project, Pi.single_apply]
    simp [Blocking.support, combined]
    exact not_congr (congrArg (fun dir => (seq idx).block.coeff row dir = 0) hh).to_iff
  · have hh : project seq idx (Pi.single ⟨other, coord⟩ 1) = 0 := by
      ext target
      simp [project, Ne.symm he]
    simp [Blocking.support, combined, Ne.symm he]
    exact (congrArg ((seq idx).block.coeff row) hh).trans (map_zero _)

theorem join_span (idx : Index) (row : (seq idx).Row) :
    (join seq).span ⟨idx, row⟩ = (seq idx).span row := by
  unfold span join
  dsimp only
  rw [support_combined, Program.join_closure, ncard_image_of_injective _ sigma_mk_injective]

theorem join_admissible {limit : ℕ} {pt : Timed (Coords seq)}
    (hp : pt ∈ (join seq).region limit) (idx : Index) :
    projectPoint seq idx pt ∈ (seq idx).region limit := by
  obtain ⟨hf, usable, hv, hs, hd⟩ := hp
  let part := @Sigma.mk _ (fun i => (seq i).prog.Coord) idx ⁻¹' usable
  let tight := (seq idx).block.system.active (projectPoint seq idx pt)
  let small := (seq idx).block.nullspace tight part
  let big := (combined seq).nullspace ((combined seq).system.active pt) usable
  refine ⟨fun row => hf ⟨idx, row⟩, part, hv idx, ?_, ?_⟩
  · intro row hr coord hc
    apply hs ⟨idx, row⟩ hr
    change Sigma.mk idx coord ∈ (combined seq).support ⟨idx, row⟩
    rw [support_combined]
    exact ⟨coord, hc, rfl⟩
  have hm : ∀ dir ∈ small, embed seq idx dir ∈ big := by
    intro dir hh
    constructor
    · rintro ⟨other, coord⟩ hn
      change project seq other (embed seq idx dir) coord = 0
      by_cases he : other = idx
      · subst other
        rw [project_embed]
        exact hh.1 coord hn
      · rw [project_embed_ne seq he]; rfl
    · apply (System.mem_directions _).mpr
      rintro ⟨other, row⟩ hr
      change (seq other).block.coeff row (project seq other (embed seq idx dir)) = 0
      by_cases he : other = idx
      · subst other
        rw [project_embed]
        exact (System.mem_directions _).mp hh.2 row hr
      · rw [project_embed_ne seq he, map_zero]
  have hi : Function.Injective ((embed seq idx).restrict hm) := by
    intro first last he
    apply Subtype.ext
    have hh := congrArg (fun v : big => project seq idx v.val) he
    simpa [project_embed] using hh
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans hd

end Package
end OAI.Geometry.Hirsch
