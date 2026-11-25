import OAI.Computability.NearSquareRoot.InterchangeCalls
import OAI.Computability.NearSquareRoot.InterchangeSpectralMask

/-!
# The recursive request of a spectral coordinate pass

A view of the two chosen fields exposes the ordinary two-field input to the
recursive interchange. Its prefix, gap and suffix are computed from the parent
header, while the view preserves the byte order of the original row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralRequest

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom InterchangeAddress

variable {I J : Type} [DecidableEq J] {b n : ℕ}
    (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ) (j : J)

noncomputable abbrev axis (i : I) :=
  twoStops ord (false,j) (true,j) (Or.inl ⟨rfl,rfl⟩)
    (p:=b) (j:=f i) (P:=P i) (G:=G i) (B:=B i)

noncomputable def child (l : I → ℕ)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (i : I) : Request b where
  before := preamble ord (P i) (G i) (field b (f i)) (false,j)
  between := silence ord (G i) (field b (f i)) (false,j) (true,j)
  after_ := appendix ord (G i) (B i) (field b (f i)) (true,j)
  width := f i
  recordWidth := l i
  contents := v i ∘ (axis ord P G B f j i).view.cast.symm

/-- The child preserves the record count, width and payload bound. -/
theorem allowed_child (l : I → ℕ)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (i : I) :
    allowed f (countRows (b:=b) ord P G B f) l i (child ord P G B f j l v i) :=
  ⟨rfl,(axis ord P G B f j i).view.cost.symm,rfl⟩

/-- Swap the two chosen physical fields, retaining every spectator in place. -/
def swapAt (j : J) {P G B : Dims.Tape} {T : Type} (x : Keys P G B J T) : Keys P G B J T :=
  (x.1, Function.update x.2.1 j (x.2.2.2.1 j), x.2.2.1,
    Function.update x.2.2.2.1 j (x.2.1 j), x.2.2.2.2)

/-- The child's answer is already in the physical record order of the parent. -/
theorem reply (l : I → ℕ)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) :
    (Request.job b).reply ∘ child ord P G B f j l v =
      stackRun (layoutRows ord P G B f) fun i x => v i (swapAt j x) := by
  funext i
  change stripe _ _ = stripe _ _
  dsimp only [child, Request.rows]
  rw [(axis (b:=b) ord P G B f j i).view.packet]
  apply congrArg (stripe _)
  funext x
  apply congrArg (v i)
  let ax := axis (b:=b) ord P G B f j i
  change ax.bridge x ((ax.pair x).2,(ax.pair x).1) = _
  have use := two_use ord (false,j) (true,j) (Or.inl ⟨rfl,rfl⟩) x (ask x (true,j)) (ask x (false,j))
  rw [show ax.pair x = (ask x (false,j),ask x (true,j)) from use.1]
  exact use.2

/-- The three child tape descriptors and its width are available from the parent header. -/
theorem child_header {r : Regime I} (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (l : I → ℕ)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) :
    r.Small (fun i => (child ord P G B f j l v i).header) := by
  have hfield := Told.carrier hb f hf
  exact hf.pair ((hfield.stair ord hp hg (false,j)).shape.pair
    ((hfield.corridor ord hg (false,j) (true,j)).shape.pair (hfield.lounge ord hg hs (true,j)).shape))

/-- Issuing the child reuses the complete physical row in its existing order. -/
theorem child_issue (l : I → ℕ) (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) :
    (Request.job b).issue ∘ child ord P G B f j l v =
      together (fun i => (child ord P G B f j l v i).header) (stackRun (layoutRows ord P G B f) v) := by
  funext i
  apply congrArg (Tree.fork _)
  change stripe _ _ = stripe _ _
  dsimp only [child, Request.rows]
  rw [(axis (b:=b) ord P G B f j i).view.packet]
  exact congrArg (stripe _) (funext fun z => congrArg (v i) ((axis ord P G B f j i).view.cast.symm_apply_apply z))

/-- Compute the child header from the parent header and attach the saved unchanged row. -/
theorem query {r : Regime I} {w : I → ℝ} (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ripe : r.ripe w)
    (l : I → ℕ) (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree)
    (row : Volume w (stackRun (layoutRows ord P G B f) v)) :
    Carries w (together r.header (stackRun (layoutRows ord P G B f) v))
      ((Request.job b).issue ∘ child ord P G B f j l v) := by
  have h := Regime.Small.cooked ripe (child_header ord P G B f j hb hf hp hg hs l v)
  have fetch := Carries.dropRight ripe.1 h.small row
  rw [child_issue]
  exact (fetch.chain h).twice (Carries.dropLeft ripe.1 h.small row)

private theorem row_volume {I R : Type} [Finite R] {D : I → Type} (s : (i : I) → Series (D i))
    (digit : R → Tree) (x : (i : I) → D i → R) (w : I → ℝ) (hw : ∀ i, 1 ≤ w i)
    (cw : ∀ i, ((s i).count : ℝ) ≤ w i) : Volume w (stackRun s fun i a => digit (x i a)) := by
  obtain ⟨U,hU⟩ := (Set.finite_range fun a => (digit a).count).bddAbove
  refine ⟨U+2, fun i => ?_⟩
  have h := stripe_size (s i) (fun a => digit (x i a)) U (fun _ => hU (Set.mem_range_self _))
  have hh : ((stripe (s i) (fun a => digit (x i a))).count : ℝ) ≤ (s i).count * ((U:ℝ)+1) + 1 := by
    exact_mod_cast h
  change ((stripe _ _).count : ℝ) ≤ _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right (cw i) (show (0:ℝ) ≤ U+1 by positivity), hw i]

/-- A complete single-field spectral program from the canonical interchange oracle
and a comparison-mask generator acting on the shape header. -/
theorem step {r : Regime I} {w : I → ℝ} (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ripe : r.ripe w)
    (cw : ∀ i, ((layoutRows (b:=b) ord P G B f i).count : ℝ) ≤ w i)
    {R : Type} [CommRing R] [Finite R] (digit : R → Tree) (hd : Function.Injective digit)
    (mark : Ordering → Tree) (hm : Function.Injective mark)
    (l : I → ℕ) (x : (i : I) → domain (J:=J) (b:=b) P G B f i → R)
    (fare : Request b → ℝ) (inverse : Bool) (half : R) :
    let points := layoutRows (b:=b) ord P G B f
    let tag := fun (i : I) (a : domain (J:=J) (b:=b) P G B f i) =>
      InterchangeSpectralStep.direction (number (a.2.1 j)) (number (a.2.2.2.1 j))
    let v := fun i a => digit (x i a)
    Carries w r.header (stackRun points fun i a => mark (tag i a)) →
    Tunnel ⟨fare,(Request.job b).issue,(Request.job b).reply⟩ w
      (fun i => [child ord P G B f j l v i]) (together r.header (stackRun points v))
      (stackRun points fun i a => digit (InterchangeSpectralStep.value inverse half (tag i a) (x i a) (x i (swapAt j a)))) := by
  intro points tag v mask
  let a := child ord P G B f j l v
  have vol := row_volume points digit x w ripe.1 cw
  have data := Carries.dropLeft ripe.1 mask.small vol
  have m := (Carries.dropRight ripe.1 mask.small vol).chain mask
  have ans : Carries w ((Request.job b).reply ∘ a) (stackRun points (fun i z => digit (x i (swapAt j z)))) := by
    rw [show (Request.job b).reply ∘ a = _ from reply ord P G B f j l v]
    exact Carries.idles ripe.1 (row_volume points digit (fun i z => x i (swapAt j z)) w ripe.1 cw)
  exact InterchangeSpectralStep.single _ a w _ points cw x (fun _ => swapAt j) tag digit mark hd hm
    data m (query ord P G B f j hb hf hp hg hs ripe l v vol) ans inverse half

private def encodeTag : Ordering → Tree
  | .lt => .atom false
  | .eq => .atom true
  | .gt => .fork (.atom false) (.atom false)

private theorem encodeTag_injective : Function.Injective encodeTag := by
  intro a c h
  cases a <;> cases c <;> simp_all [encodeTag]

variable {R : Type} [CommRing R]

/-- One lookup on an occupied record in the physical address layout. -/
def advance {b f : ℕ} {P G B : Dims.Tape} (inv : Bool) (half : R) (j : J)
    (x : Keys P G B J (Block b f) → R) (a : Keys P G B J (Block b f)) : R :=
  InterchangeSpectralStep.value inv half
    (InterchangeSpectralStep.direction (number (a.2.1 j)) (number (a.2.2.2.1 j)))
    (x a) (x (swapAt j a))

/-- The actual query emitted at each pass uses the values returned by the preceding pass. -/
noncomputable def ledger (inverse : Bool) (half : R) (digit : R → Tree) (l : I → ℕ) :
    List J → ((i : I) → domain (J:=J) (b:=b) P G B f i → R) → I → List (Request b)
  | [], _, _ => []
  | j :: rest, x, i => child ord P G B f j l (fun t a => digit (x t a)) i ::
      ledger inverse half digit l rest (fun t => advance inverse half j (x t)) i

theorem ledger_length (inverse : Bool) (half : R) (digit : R → Tree) (l : I → ℕ)
    (fields : List J) (x : (i : I) → domain (J:=J) (b:=b) P G B f i → R) (i : I) :
    (ledger ord P G B f inverse half digit l fields x i).length = fields.length := by
  induction fields generalizing x with
  | nil => rfl
  | cons j js ih => simp [ledger, ih]

theorem ledger_allowed (inverse : Bool) (half : R) (digit : R → Tree) (l : I → ℕ)
    (fields : List J) (x : (i : I) → domain (J:=J) (b:=b) P G B f i → R) (i : I)
    (a : Request b) (ha : a ∈ ledger ord P G B f inverse half digit l fields x i) :
    allowed f (countRows (b:=b) ord P G B f) l i a := by
  induction fields generalizing x with
  | nil => cases ha
  | cons j js ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact allowed_child ord P G B f j l _ i
    · exact ih _ h

/-- Generate every comparison mask, issue one actual two-field request per listed
coordinate, return the transformed row in its original layout and restore the header. -/
theorem run [NeZero b] [Finite R] {r : Regime I} {w : I → ℝ}
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (ripe : r.ripe w) (cw : ∀ i, ((layoutRows (b:=b) ord P G B f i).count : ℝ) ≤ w i)
    (inverse : Bool) (half : R) (digit : R → Tree) (hd : Function.Injective digit)
    (l : I → ℕ) (fare : Request b → ℝ) (fields : List J)
    (x : (i : I) → domain (J:=J) (b:=b) P G B f i → R) :
    let packed := fun (v : (i : I) → domain (J:=J) (b:=b) P G B f i → R) =>
      together r.header (stackRun (layoutRows ord P G B f) fun i a => digit (v i a))
    Tunnel ⟨fare,(Request.job b).issue,(Request.job b).reply⟩ w
      (ledger ord P G B f inverse half digit l fields x) (packed x)
      (packed (fun i => fields.foldl (fun g j => advance inverse half j g) (x i))) := by
  intro packed
  let points := layoutRows (b:=b) ord P G B f
  let vol := row_volume points digit
  let hhead := (Regime.Small.cooked ripe (Regime.self (r:=r))).small
  induction fields generalizing x with
  | nil =>
    have z := Carries.idles ripe.1 (hhead.fork (vol x w ripe.1 cw) ripe.1)
    exact Tunnel.walkway z.runs
  | cons j rest ih =>
    let y i := advance inverse half j (x i)
    have m := SpectralMask.layout_program ord P G B f j hb hf hp hg hs ripe cw encodeTag
    have head := step ord P G B f j hb hf hp hg hs ripe cw digit hd encodeTag encodeTag_injective
      l x fare inverse half m
    have hv := vol x w ripe.1 cw
    have hy := vol y w ripe.1 cw
    have stash := (Carries.idles ripe.1 (hhead.fork hv ripe.1)).twice (Carries.dropRight ripe.1 hhead hv)
    have fixup := (Carries.dropLeft ripe.1 hy hhead).twice (Carries.dropRight ripe.1 hy hhead)
    have saved := ((Tunnel.walkway (o:=⟨fare,(Request.job b).issue,(Request.job b).reply⟩) stash.runs).join
      (head.surround r.header)).join (Tunnel.walkway fixup.runs)
    have all := saved.join (ih y)
    exact all

/-- Numerical field labels index the occupied address cells in increasing order. -/
noncomputable def fieldRank (b f : ℕ) [NeZero b] : Block b f ≃ Fin (b^f) :=
  Equiv.ofBijective (fun a => ⟨number a, number_lt a⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => number_inj _ _ (congrArg Fin.val h), by rw [Adic.count, Fintype.card_fin]⟩)

@[simp] theorem number_rank_symm {b f : ℕ} [NeZero b] (k : Fin (b^f)) :
    number ((fieldRank b f).symm k) = k.val :=
  congrArg Fin.val ((fieldRank b f).apply_symm_apply k)

/-- Reconstruct the physical address at a fixed triplet of spectators. -/
noncomputable def key {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (a : SwapSpectrum.Address J (Fin (b^f))) : Keys P G B J (Block b f) :=
  (p, fun j => (fieldRank b f).symm (a j).1, g, fun j => (fieldRank b f).symm (a j).2, s)

private theorem key_swap {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (a : SwapSpectrum.Address J (Fin (b^f))) (j : J) :
    key p g s (SwapSpectrum.swap j a) = swapAt j (key p g s a) := by
  simp only [key, swapAt, Prod.mk.injEq, true_and, and_true]
  constructor
  · funext k
    by_cases h : k = j
    · subst k; simp
    · simp [SwapSpectrum.swap_other h, Function.update_of_ne h]
  · funext k
    by_cases h : k = j
    · subst k; simp
    · simp [SwapSpectrum.swap_other h, Function.update_of_ne h]

private theorem advance_key {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (inverse : Bool) (half : R) (x : Keys P G B J (Block b f) → R) (j : J)
    (a : SwapSpectrum.Address J (Fin (b^f))) :
    advance inverse half j x (key p g s a) =
      InterchangeSpectralStep.value inverse half (InterchangeSpectralStep.direction (a j).1 (a j).2)
        (x (key p g s a)) (x (key p g s (SwapSpectrum.swap j a))) := by
  unfold advance
  rw [key_swap]
  congr 1
  simp only [key, number_rank_symm, InterchangeSpectralStep.direction, Fin.val_inj]
  rfl

/-- At each spectator the physical pass over a field list agrees with the algebraic
sum/difference transform on its numerical address cube. -/
theorem passes_key {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (inverse : Bool) (half : R) (fields : List J) (x : Keys P G B J (Block b f) → R) :
    (fields.foldl (fun v j => advance inverse half j v) x) ∘ key p g s =
      InterchangeSpectralStep.passes inverse half fields (x ∘ key p g s) := by
  induction fields generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons, InterchangeSpectralStep.passes] at *
    rw [ih]
    congr 1
    exact funext (advance_key p g s inverse half x j)

/-- Spectral meaning of the P192 program in forward order. -/
theorem forward_key {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (half : R) (hh : 2 * half = 1) (fields : List J) (x : Keys P G B J (Block b f) → R) :
    (fields.foldl (fun v j => advance false half j v) x) ∘ key p g s =
      SwapSpectrum.spectrum fields half hh (x ∘ key p g s) :=
  (passes_key p g s false half fields x).trans (InterchangeSpectralStep.forward_passes ..)

/-- Spectral meaning of the P192 program in reverse order. -/
theorem inverse_key {b f : ℕ} [NeZero b] {P G B : Dims.Tape} (p : Pin P) (g : Pin G) (s : Pin B)
    (half : R) (hh : 2 * half = 1) (fields : List J) (x : Keys P G B J (Block b f) → R) :
    (fields.reverse.foldl (fun v j => advance true half j v) x) ∘ key p g s =
      (SwapSpectrum.spectrum fields half hh).symm (x ∘ key p g s) :=
  (passes_key p g s true half fields.reverse x).trans (InterchangeSpectralStep.inverse_passes ..)

end InterchangeSpectralRequest

end NearSquareRoot
end Computability
end OAI
