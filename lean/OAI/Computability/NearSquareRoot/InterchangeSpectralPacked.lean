import OAI.Computability.NearSquareRoot.InterchangeSpectralRequest
import OAI.Computability.NearSquareRoot.InterchangePayloadBank
import OAI.Computability.NearSquareRoot.InterchangeSpectralPackedCell

/-!
# Spectral conversion of packed payloads

All payload positions of one outer address travel together in a single
two-field interchange request. The table acts at each payload position.
The local charge is the outer count times the payload width plus a single
polynomial in the descriptor size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralPacked

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeSpectralRequest

variable {I J R : Type} [DecidableEq J] [CommRing R] {b n : ℕ}
    (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ) {D : I → Type}
    (payload : (i : I) → Series (D i)) (digit : R → Tree)

abbrev Values (b : ℕ) (J : Type) (D : I → Type) :=
  (i : I) → D i → domain (J:=J) (b:=b) P G B f i → R

/-- The symbol stream in one physical record. -/
def pack (x : Values P G B f b J D (R:=R)) (i : I) (a : domain (J:=J) (b:=b) P G B f i) :=
  stripe (payload i) fun d => digit (x i d a)

/-- Payload positions travel together through every interchange in the list. -/
noncomputable def children (l : I → ℕ) (inverse : Bool) (half : R) :
    List J → Values P G B f b J D (R:=R) → I → List (Request b)
  | [], _, _ => []
  | j :: js, x, i =>
    child ord P G B f j l (pack P G B f payload digit x) i ::
      children l inverse half js (fun t d => advance inverse half j (x t d)) i

theorem children_length (l : I → ℕ) (inverse : Bool) (half : R) (fields : List J)
    (x : Values P G B f b J D (R:=R)) (i : I) :
    (children ord P G B f payload digit l inverse half fields x i).length = fields.length := by
  induction fields generalizing x with
  | nil => rfl
  | cons j js ih => simp [children, ih]

private theorem inherits (l : I → ℕ) (j : J)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (i : I) :
    inherited b (P i) (G i) (B i) (child ord P G B f j l v i) := by
  intro k hk
  dsimp only [child] at hk
  simp only [preamble_false,silence_false_true,appendix_true,List.mem_append] at hk
  simp only [List.mem_append]
  rcases hk with (((hp | h₁) | h₂ | hg | h₃) | h₄ | hs)
  · exact .inr (.inl (.inl hp))
  · exact .inl (source_radix k _ b _ h₁)
  · exact .inl (source_radix k _ b _ h₂)
  · exact .inr (.inl (.inr hg))
  · exact .inl (source_radix k _ b _ h₃)
  · exact .inl (source_radix k _ b _ h₄)
  · exact .inr (.inr hs)

/-- Every recursive call preserves the record count, field width, payload shape
and alphabet. Its tape dimensions come from the parent or the underlying radix. -/
theorem children_typed (l : I → ℕ) (inverse : Bool) (half : R) (fields : List J)
    (x : Values P G B f b J D (R:=R)) (i : I) (a : Request b)
    (ha : a ∈ children ord P G B f payload digit l inverse half fields x i) :
    (allowed f (countRows (b:=b) ord P G B f) l i a ∧
      ∀ k, InterchangePayloadBank.Good payload digit i (a.contents k)) ∧
    inherited b (P i) (G i) (B i) a := by
  induction fields generalizing x with
  | nil => cases ha
  | cons j js ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a
      exact ⟨⟨allowed_child ord P G B f j l _ i, fun _ => ⟨_, rfl⟩⟩, inherits ord P G B f l j _ i⟩
    · exact ih _ h

private def mark : Ordering → Tree
  | .lt => .atom false
  | .eq => .atom true
  | .gt => .fork (.atom false) (.atom false)

private theorem mark_inj : Function.Injective mark := by
  intro a b h
  cases a <;> cases b <;> simp_all [mark]

/-- Combined length of the record stream and its payloads. -/
abbrev work (l : I → ℕ) (i : I) := countRows (b:=b) ord P G B f i * (l i+1)

omit [DecidableEq J] in
private theorem mask_rip [NeZero b] {r : Regime I} (j : J)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B) (l : I → ℕ) :
    Rip r (fun _ => 1) (work (b:=b) ord P G B f l) r.header
      (stackRun (layoutRows (b:=b) ord P G B f) fun _ x =>
        mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j)))) := by
  obtain ⟨k,mask⟩ := SpectralMask.layout_with_setup ord P G B f j hb hf hp hg hs mark
  refine ⟨k, mask.larger ?_⟩
  intro i
  simp only [mass, Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_pow]
  gcongr
  exact_mod_cast (Nat.le_mul_of_pos_right (countRows (b:=b) ord P G B f i) (Nat.succ_pos (l i)))

omit [DecidableEq J] in
private theorem cost_bound {r : Regime I} (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (k : ℕ) (i : I) :
    ((layoutRows (b:=b) ord P G B f i).count : ℝ) * ((payload i).count + 1) ≤
      mass r (fun _ => 1) (work (b:=b) ord P G B f l) k i := by
  simp only [mass, Nat.cast_one, one_mul, work, Nat.cast_mul, Nat.cast_add]
  apply le_add_of_le_of_nonneg _ (by positivity)
  gcongr
  exact_mod_cast h i

omit [DecidableEq J] [CommRing R] in
private theorem alive [Finite R] {r : Regime I} (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i)
    (x : Values P G B f b J D (R:=R)) :
    Alive r (fun _ => 1) (work (b:=b) ord P G B f l)
      (stackRun (layoutRows ord P G B f) (pack P G B f payload digit x)) := by
  have hw := unit_mass (r:=r) (l:=work (b:=b) ord P G B f l) (fun _ : I => le_refl 1) 0
  exact ⟨0,Carries.idles hw (InterchangeSpectralPackedCell.row_volume _ payload digit
    (fun i a d => x i d a) _ hw (cost_bound ord P G B f payload l h 0))⟩

private theorem single [NeZero b] [Finite R] {r : Regime I} (j : J) (hb : 2 ≤ b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (hd : Function.Injective digit)
    (inv : Bool) (half : R) (x : Values P G B f b J D (R:=R)) :
    let points := layoutRows (b:=b) ord P G B f
    let row := fun y => stackRun points (pack P G B f payload digit y)
    let a := child ord P G B f j l (pack P G B f payload digit x)
    Quest (Request.job b) r (fun _ => 1) (work (b:=b) ord P G B f l) (fun i => [a i])
      (together r.header (row x))
      (row (fun i d => advance inv half j (x i d))) := by
  intro points row a
  let W := work (b:=b) ord P G B f l
  let tag (i : I) (z : domain (J:=J) (b:=b) P G B f i) :=
    InterchangeSpectralStep.direction (number (z.2.1 j)) (number (z.2.2.2.1 j))
  let mask := stackRun points fun i z => mark (tag i z)
  let y (i : I) (d : D i) (z : domain (J:=J) (b:=b) P G B f i) := x i d (swapAt j z)
  let live := alive (r:=r) (b:=b) ord P G B f payload digit l h
  have inRow := Drive.self (fun _ : I => le_refl 1) (live x)
  have inHdr := Drive.fetch (fun _ : I => le_refl 1) (live x)
  have maskRead : Rip r (fun _ => 1) W r.header mask := mask_rip ord P G B f j hb hf hp hg hs l
  have source : Rip r (fun _ => 1) W (together r.header (row x)) ((Request.job b).issue ∘ a) := by
    rw [show (Request.job b).issue ∘ a = _ from child_issue ord P G B f j l _]
    exact (inHdr.chain (Rip.header (fun _ : I => le_refl 1)
      (child_header ord P G B f j hb hf hp hg hs l _))).twice inRow
  have call := (Quest.board (j:=Request.job b) a (fun _ : I => le_refl 1)).hand source
  have post : (Request.job b).reply ∘ a = row y := reply ord P G B f j l _
  rw [post] at call
  have parked := inRow.twice (inHdr.chain maskRead)
  have issued := call.widen (together (row x) mask) parked
  apply issued.transfer
  have all := Rip.split (Rip.alivePair (live y) parked.idle)
  obtain ⟨s,hy⟩ := all.1
  obtain ⟨t,hx⟩ := (Rip.split all.2).1
  obtain ⟨u,ht⟩ := (Rip.split all.2).2
  let k := s+t+u
  apply Exists.intro k
  exact InterchangeSpectralPackedCell.combine points payload (fun i a d => x i d a)
    (fun i a d => y i d a) tag digit mark hd mark_inj inv half
    (cost_bound ord P G B f payload l h k)
    (hx.larger (mass_le (by dsimp [k]; omega : t ≤ k)))
    (hy.larger (mass_le (by dsimp [k]; omega : s ≤ k)))
    (ht.larger (mass_le (by dsimp [k]; omega : u ≤ k)))

/-- A packed spectral conversion, with one child on the whole payload for each field.
Its local budget is the physical volume plus a single polynomial in the parent header. -/
theorem run [NeZero b] [Finite R] {r : Regime I} (hb : 2 ≤ b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (hd : Function.Injective digit)
    (inv : Bool) (half : R) (fields : List J) (x : Values P G B f b J D (R:=R)) :
    let packet := fun y => together r.header (stackRun (layoutRows ord P G B f) (pack P G B f payload digit y))
    Quest (Request.job b) r (fun _ => 1) (work (b:=b) ord P G B f l)
      (children ord P G B f payload digit l inv half fields x) (packet x)
      (packet (fun i d => fields.foldl (fun g j => advance inv half j g) (x i d))) := by
  intro packet
  let W := work (b:=b) ord P G B f l
  let live := alive (r:=r) (b:=b) ord P G B f payload digit l h
  let hh := Drive.started (r:=r) (l:=W) (fun _ : I => le_refl 1)
  induction fields generalizing x with
  | nil => exact Quest.entry (Rip.alivePair hh (live x))
  | cons j js ih =>
    let y i d := advance inv half j (x i d)
    have head := single ord P G B f payload digit j hb hf hp hg hs l h hd inv half x
    have keep := head.widen r.header (Drive.fetch (fun _ : I => le_refl 1) (live x))
    have both := Rip.split (Rip.alivePair (live y) hh)
    exact (keep.transfer (both.2.twice both.1)).seam (ih y)

/-- Move a one-time setup allowance into the ordinary P192 per-record mass.
This only changes the fixed local time constant. Oracle fares retain their coefficients. -/
private theorem charge {X : Type} (o : Oracle X) (r : Regime I) (N l : I → ℕ)
    {k : ℕ} {a : I → List X} {u v : I → Tree} (pos : ∀ i, 1 ≤ N i)
    (z : Tunnel o (mass r (fun _ => 1) (fun i => N i * (l i+1)) k) a u v) :
    Tunnel o (mass r N l k) a u v := by
  obtain ⟨_,c,U,run⟩ := z
  refine ⟨unit_mass pos k,c,2*U,fun i parent env D allow j => ?_⟩
  apply (run i parent env D allow j).mono
  have hn : (1:ℝ) ≤ N i := by exact_mod_cast pos i
  let S : ℝ := (r.scale i + 1 : ℝ)^k
  have hS : 1 ≤ S := one_le_pow₀ (by simp)
  have bound : mass r (fun _ => 1) (fun i => N i * (l i+1)) k i ≤ 2 * mass r N l k i := by
    simp only [mass, Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_mul]
    change (N i : ℝ) * (l i + 1) + S ≤ 2 * (N i * (l i + S))
    have term₁ := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg (α:=ℝ) (N i))
    have term₂ := le_mul_of_one_le_left (by linarith : 0 ≤ S) hn
    nlinarith [(Nat.cast_mul (α:=ℝ) (N i) (l i)), Nat.cast_nonneg (α:=ℝ) (N i * l i)]
  push_cast
  linarith [mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg (α:=ℝ) U),
    show (2:ℝ)*U*mass r N l k i = U*(2*mass r N l k i) by ring]

/-- The full packed conversion in the address compiler's typed-call interface.
The output is a bare row packet, ready for an ordinary stage. -/
theorem charged [NeZero b] [Finite R] {r : Regime I} (hb : 2 ≤ b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (hd : Function.Injective digit)
    (inv : Bool) (half : R) (fields : List J) (x : Values P G B f b J D (R:=R)) :
    let row := fun y => stackRun (layoutRows ord P G B f) (pack P G B f payload digit y)
    ChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      fields.length (row x) (row (fun i d => fields.foldl (fun g j => advance inv half j g) (x i d))) := by
  intro row
  let y i d := fields.foldl (fun g j => advance inv half j g) (x i d)
  have z := run ord P G B f payload digit hb hf hp hg hs l h hd inv half fields x
  have done := z.transfer (Drive.self (fun _ : I => le_refl 1) (alive ord P G B f payload digit l h y))
  let a := children ord P G B f payload digit l inv half fields x
  refine ⟨a,fun i v hv => children_typed ord P G B f payload digit l inv half fields x i v hv,
    fun i => ?_,?_⟩
  · simp [a, children_length]
  · obtain ⟨k, body⟩ := done.eligible
    exact ⟨k, fun e => charge _ r _ l (layoutRows_station ord P G B f hb hf hp hg hs).1 (body e)⟩

end InterchangeSpectralPacked

end NearSquareRoot
end Computability
end OAI
