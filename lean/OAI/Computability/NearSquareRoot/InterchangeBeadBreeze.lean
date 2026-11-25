import OAI.Computability.NearSquareRoot.InterchangeBeadPadding
import OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-!
# Running a thick interchange on arbitrary bead records

The outer header provides a polynomial-size prefix of known length, copied
to every row. After the recursive swap its inverse removes this prefix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request

noncomputable section

private theorem packed_list {F : Type} [Field F] [Finite F] [DecidableEq F] (l : List Bead) :
    record (beadDigit (F:=F)) l.length (send l) := by
  let u := Series.natural l.length
  let v := u.untab l (Series.count_natural l.length).symm
  have eq := u.recover l (Series.count_natural l.length).symm
  have h := bead_record (F:=F) u v
  simpa only [Function.comp_def, stripe_eq', v, eq, u, Series.count_natural] using h

theorem padded_fare {I : Type} {r : Regime I} (N L u pad e : I → ℕ)
    (fit : ∀ i, u i ≤ L i) (dom : Dom r.scale pad) (α : ℝ) (hα : 0 ≤ α) :
    ∃ k C : ℕ, ∀ i,
      (N i : ℝ) * ((pad i + u i + 1 : ℕ) : ℝ) * (e i : ℝ)^α ≤
        (C : ℝ) * runrate (Spindle.modes e (τ:=α)) r N L k i := by
  obtain ⟨k,C,h⟩ := dom
  refine ⟨k,C+2,fun i => ?_⟩
  let scale := r.scale i + 1
  have power : 1 ≤ scale ^ k := Nat.one_le_pow _ _ (by dsimp [scale]; omega)
  have d : pad i + u i + 1 ≤ (C+2)*(L i + scale^k) := by
    have hz := h i
    change pad i ≤ C * scale ^ k at hz
    have := fit i
    rw [Nat.add_mul,Nat.mul_add]
    omega
  have growth : (e i : ℝ)^α ≤ Spindle.modes e (τ:=α) i := by
    apply Real.rpow_le_rpow (by positivity) _ hα
    exact_mod_cast Nat.le_succ _
  have d' : ((pad i + u i + 1 : ℕ) : ℝ) ≤
      ((C+2 : ℕ):ℝ) * ((L i:ℝ) + (r.scale i+1 : ℝ)^k) := by exact_mod_cast d
  calc
    _ ≤ ((N i : ℝ) * (((C+2:ℕ):ℝ) * ((L i:ℝ) + (r.scale i+1:ℝ)^k))) *
        Spindle.modes e (τ:=α) i := mul_le_mul
      (mul_le_mul_of_nonneg_left d' (Nat.cast_nonneg _)) growth
      (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by unfold runrate mass; ring

variable {I F : Type} {b : ℕ} [Field F] [Finite F] [DecidableEq F]
    {r : Regime I} {α : ℝ}

/-- Prepare an actual certified request and recover the ordinary bead cloth from
its reply. The record volume and active width are kept explicit for applying
either the time-only solver or the joint time-and-space solver. -/
theorem bead_parts (hb : 2 ≤ b) (k : ℕ)
    (P G B : I → Tape) (e : I → ℕ) (pos : ∀ i, 0 < e i) (he : r.Has (tally ∘ e))
    (hp : Told r P) (hg : Told r G) (hb' : Told r B)
    (radices : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ b)
    (L : I → ℕ) {T : I → Type} (u : (i : I) → Series (T i)) (fit : ∀ i, (u i).count ≤ L i)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block b (e i)) → T i → Bead)
    (pad : I → ℕ) (hpad : r.Has (tally ∘ pad))
    (thick : ∀ i, (Nat.log 2 (stock b (P i) (G i) (B i) (e i)).count + 1)^k ≤ pad i) :
    let s i := stock b (P i) (G i) (B i) (e i)
    let N i := (s i).count
    let input := together r.header (cloth s u v)
    let output := cloth s u fun i a => v i (swapper _ _ _ a)
    ∃ q : I → ThickRequest (Packed (beadDigit (F:=F))) k,
      (∀ i, (q i).val.recordVolume = N i * (pad i + (u i).count + 1)) ∧
      (∀ i, (q i).val.width = e i) ∧
      Rip r N L input (fun i => (job b).issue (q i).val) ∧ Rip r N L input r.header ∧
      Rip r N L (together r.header (fun i => (job b).reply (q i).val)) output := by
  intro s N input output
  let Y i a := v i (swapper _ _ _ a)
  have fstation := (Told.carrier hb e he).station
  have st : Station r s :=
    hp.station.product (fstation.product (hg.station.product (fstation.product hb'.station)))
  have pre := (BeadPadding.charge s st pad hpad u v fit).1
  have post := (BeadPadding.charge s st pad hpad u Y fit).2
  let req (i : I) : Request b :=
    ⟨P i,G i,B i,e i,pad i+(u i).count,fun a => send (BeadPadding.padded pad u v i a)⟩
  have admissible (i : I) : Admissible (req i) := by
    intro d hd
    refine ⟨?_,radices i d hd⟩
    rcases List.mem_append.mp hd with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hp.solid i d h
      · exact hg.solid i d h
    · exact hb'.solid i d h
  let select (i : I) : ThickRequest (Packed (beadDigit (F:=F))) k :=
    ⟨req i,⟨⟨admissible i,pos i,fun a => by
      have row := packed_list (F:=F) (BeadPadding.padded pad u v i a)
      change record _ (pad i + (u i).count) (send (BeadPadding.padded pad u v i a))
      simpa only [BeadPadding.padded,BeadPadding.words,List.length_append,List.length_replicate,Series.card] using row⟩,
      (thick i).trans (by change pad i ≤ pad i + (u i).count + 1; omega)⟩⟩
  have header : r.Small (fun i => (req i).header) :=
    he.pair (hp.shape.pair (hg.shape.pair hb'.shape))
  have plain := cloth_size s u st v fit
  have read := Drive.fetch st.1 plain
  have arrange : Rip r N L (together r.header (cloth s u v)) (fun i => (job b).issue (req i)) :=
    (read.designed st.1 header).twice pre
  exact ⟨select,fun _ => rfl,fun _ => rfl,arrange,read,post⟩

/-- The supplied radix program may only accept records meeting its single
degree threshold. All rows of the output retain their original lengths. -/
theorem radixBeadBreeze (hb : 2 ≤ b) (hα : 0 ≤ α) (k : ℕ)
    (run : Sized (fun x : ThickRequest (b:=b) (Packed (beadDigit (F:=F))) k =>
        (x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α)
      (fun x => (job b).issue x.val) (fun x => (job b).reply x.val))
    (P G B : I → Tape) (e : I → ℕ) (pos : ∀ i, 0 < e i) (he : r.Has (tally ∘ e))
    (hp : Told r P) (hg : Told r G) (hb' : Told r B)
    (radices : ∀ i d, d ∈ P i ++ G i ++ B i → d ≤ b)
    (L : I → ℕ) {T : I → Type} (u : (i : I) → Series (T i)) (fit : ∀ i, (u i).count ≤ L i)
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block b (e i)) → T i → Bead)
    (pad : I → ℕ) (hpad : r.Has (tally ∘ pad)) (dom : Dom r.scale pad)
    (thick : ∀ i, (Nat.log 2 (stock b (P i) (G i) (B i) (e i)).count + 1)^k ≤ pad i) :
    let s i := stock b (P i) (G i) (B i) (e i)
    Breeze (Spindle.modes e (τ:=α)) r (fun i => (s i).count) L
      (together r.header (cloth s u v)) (cloth s u fun i a => v i (swapper _ _ _ a)) := by
  intro s
  let N i := (s i).count
  let rate := Spindle.modes e (τ:=α)
  have hrate := Spindle.belly (t:=e) hα
  obtain ⟨select,volume,width,arrange,read,post⟩ :=
    bead_parts (F:=F) hb k P G B e pos he hp hg hb' radices L u fit v pad hpad thick
  obtain ⟨j, start⟩ := arrange
  obtain ⟨d,C,bound⟩ := padded_fare (r:=r) N L (fun i => (u i).count) pad e fit dom α hα
  let work := runrate rate r N L (j+d)
  have massGrowth i : mass r N L j i ≤ work i :=
    (mass_le (by omega : j ≤ j+d) i).trans (le_mul_of_one_le_right
      (by unfold mass; positivity) (hrate i))
  have ready := start.larger massGrowth
  have timed := (run.along select).adapts ready.budget C (fun i => by
    rw [volume,width,Nat.cast_mul]
    exact (bound i).trans (mul_le_mul_of_nonneg_left
      (rate_higher i (hrate i) (by omega : d ≤ j+d)) (Nat.cast_nonneg _)))
  have central : Breeze rate r N L (together r.header (cloth s u v))
      (fun i => (job b).reply (select i).val) := ⟨hrate,j+d,ready.sequence timed⟩
  exact ((Breeze.launch read hrate).pair central).next (Breeze.launch post hrate)

end
end InterchangePayload

end NearSquareRoot
end Computability
end OAI
