import OAI.Computability.NearSquareRoot.InterchangeBQuestAddress
import OAI.Computability.NearSquareRoot.InterchangeSpectralPacked

/-!
# Space-bounded spectral sweeps on packed records

At each field the sweep retains the original row and its comparison mask
while the recursive interchange supplies the swapped row. The local table
then combines these three streams at the same payload width. Every field
charges one recursive call with the inherited address dimensions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralPacked

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeSpectralRequest InterchangeSpace

variable {I J R : Type} [DecidableEq J] [CommRing R] {b n : ℕ}
    (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ) {D : I → Type}
    (payload : (i : I) → Series (D i)) (digit : R → Tree)

open private mark mark_inj from OAI.Computability.NearSquareRoot.InterchangeSpectralPacked

omit [DecidableEq J] in
private theorem comparison_mask [NeZero b] {r : Regime I} (l : I → ℕ) (j : J)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B) :
    Rip r (countRows (b:=b) ord P G B f) l r.header
      (stackRun (layoutRows (b:=b) ord P G B f) fun _ x =>
        mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j)))) := by
  have pos := (layoutRows_station (b:=b) ord P G B f hb hf hp hg hs).1
  obtain ⟨k,mask⟩ := SpectralMask.layout_with_setup ord P G B f j hb hf hp hg hs mark
  refine ⟨k, mask.times (unit_mass pos k) 2 (fun i => ?_)⟩
  let N := countRows (b:=b) ord P G B f i
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast pos i
  have hpow : (1 : ℝ) ≤ ((r.scale i : ℝ) + 1)^k := one_le_pow₀ (by simp)
  simp only [mass, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  change (N : ℝ) + ((r.scale i : ℝ) + 1)^k ≤ 2*(N * ((l i : ℝ) + ((r.scale i : ℝ) + 1)^k))
  have h₁ := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ N) hpow
  have h₂ := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ ((r.scale i : ℝ)+1)^k) hn
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ N) (Nat.cast_nonneg (α:=ℝ) (l i))]

private theorem bounded_field [NeZero b] [Finite R] {r : Regime I} (j : J) (hb : 2 ≤ b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (hd : Function.Injective digit)
    (inv : Bool) (half : R) (x : Values P G B f b J D (R:=R)) :
    let row := fun y => stackRun (layoutRows ord P G B f) (pack P G B f payload digit y)
    BChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      1 (row x) (row (fun i d => advance inv half j (x i d))) := by
  intro row
  let points := layoutRows (b:=b) ord P G B f
  let a := child ord P G B f j l (pack P G B f payload digit x)
  let tag (i : I) (z : domain (J:=J) (b:=b) P G B f i) :=
    InterchangeSpectralStep.direction (number (z.2.1 j)) (number (z.2.2.2.1 j))
  let mask := stackRun points fun i z => mark (tag i z)
  let y (i : I) (d : D i) (z : domain (J:=J) (b:=b) P G B f i) := x i d (swapAt j z)
  have st := layoutRows_station (b:=b) ord P G B f hb hf hp hg hs
  have live u : Alive r (countRows (b:=b) ord P G B f) l (row u) :=
    (InterchangePayloadBank.manifest payload digit (fun i z => u i z.2 z.1) h).lives st
  have inRow := Drive.self st.1 (live x)
  have inHdr := Drive.fetch st.1 (live x)
  have parked := inRow.twice (inHdr.chain (comparison_mask ord P G B f l j hb hf hp hg hs))
  have source : Drive r (countRows (b:=b) ord P G B f) l (row x) ((Request.job b).issue ∘ a) := by
    rw [show (Request.job b).issue ∘ a = _ from child_issue ord P G B f j l _]
    exact (inHdr.chain (Rip.header st.1 (child_header ord P G B f j hb hf hp hg hs l _))).twice inRow
  have call : BChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      1 (row x) (row y) := by
    unfold BChargedTyped
    rw [← show (Request.job b).reply ∘ a = row y from reply ord P G B f j l _]
    apply (BHop.summon a ?_).preceded source
    intro i
    exact children_typed ord P G B f payload digit l inv half [j] x i (a i) List.mem_cons_self
  have both := call.doubleg (BHop.tarry parked) inRow.again (live y) parked.idle
  rw [Int.add_zero] at both
  apply both.afterTask
  have all := Rip.split (Rip.alivePair (live y) parked.idle)
  obtain ⟨s,hy⟩ := all.1
  obtain ⟨t,hx⟩ := (Rip.split all.2).1
  obtain ⟨u,ht⟩ := (Rip.split all.2).2
  let k := s+t+u
  refine ⟨k,InterchangeSpectralPackedCell.combine points payload (fun i a d => x i d a)
    (fun i a d => y i d a) tag digit mark hd mark_inj inv half (fun i => ?_)
    (hx.larger (mass_le (by dsimp [k]; omega : t ≤ k)))
    (hy.larger (mass_le (by dsimp [k]; omega : s ≤ k)))
    (ht.larger (mass_le (by dsimp [k]; omega : u ≤ k)))⟩
  unfold mass
  have hpow : (1 : ℝ) ≤ ((r.scale i : ℝ)+1)^k := one_le_pow₀ (by simp)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact add_le_add (by exact_mod_cast h i) hpow

/-- The sweep makes one typed child request for each field and keeps
only a bounded set of parent streams live between calls. -/
theorem bounded_charged [NeZero b] [Finite R] {r : Regime I} (hb : 2 ≤ b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (l : I → ℕ) (h : ∀ i, (payload i).count ≤ l i) (hd : Function.Injective digit)
    (inv : Bool) (half : R) (fields : List J) (x : Values P G B f b J D (R:=R)) :
    let row := fun y => stackRun (layoutRows ord P G B f) (pack P G B f payload digit y)
    BChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      fields.length (row x) (row (fun i d => fields.foldl (fun g j => advance inv half j g) (x i d))) := by
  intro row
  have st := layoutRows_station (b:=b) ord P G B f hb hf hp hg hs
  have live u : Alive r (countRows (b:=b) ord P G B f) l (row u) :=
    (InterchangePayloadBank.manifest payload digit (fun i z => u i z.2 z.1) h).lives st
  induction fields generalizing x with
  | nil => exact BHop.tarry (Drive.self st.1 (live x))
  | cons j js ih =>
    let y i d := advance inv half j (x i d)
    have head := bounded_field ord P G B f payload digit j hb hf hp hg hs l h hd inv half x
    have all := BHop.sequence st.1 (live x) (live y) head (ih y)
    simpa only [BChargedTyped,List.length_cons,List.foldl_cons,y,countRows,Nat.cast_add,Nat.cast_one,add_comm] using all

end InterchangeSpectralPacked

end NearSquareRoot
end Computability
end OAI
