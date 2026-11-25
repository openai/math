import OAI.Computability.BorderVNP.DiagonalTallyRAMResult

/-!
# Installing the native tally stage on disjoint word intervals

Only the input memory and the numerical interval endpoints need to be checked by the
caller. The emitted instructions preserve their directory, the still unread common bits,
and every local count outside a written interval.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyScatter

variable {w : ℕ}

/-- Disjoint half-open physical intervals, allowing either physical ordering. -/
def separated (base len base' len' : ℕ) : Prop :=
  base+len ≤ base' ∨ base'+len' ≤ base

private theorem outside_of_separated {a b x y i : ℕ} (hs : separated a b x y)
    (hl : x ≤ i) (hu : i < x+y) : i < a ∨ a+b ≤ i := by
  rcases hs with h | h <;> omega

private theorem scatter_outside (m : Memory w) (base dim i : ℕ) (rs : List (ℕ × ℕ))
    (hs : ∀ r ∈ rs, r.1 < dim) (ho : i < base ∨ base+dim ≤ i) : after base rs m i = m i := by
  have hz : incrementAt base i rs = 0 := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      have hc := hs r List.mem_cons_self
      have he : base+r.1 ≠ i := by omega
      simp only [incrementAt,he,ite_false,zero_add]
      exact ih (fun x hx => hs x (.tail _ hx))
  simp [DiagonalTallyScatter.after,hz,word]

private theorem resident_congr (f : Frame) (pub : Arg → Word w) (m m' : Memory w)
    (hr : f.resident pub m)
    (he : ∀ j, (pub 0).val+32 ≤ j → j < (pub 0).val+44 → m' j = m j) :
    f.resident pub m' := by
  dsimp [Frame.resident] at *
  repeat' rw [he _ (by omega) (by omega)]
  exact hr

/-- Build the execution input from the initial directory, records, and common bit buffer,
using disjoint address intervals. No proof about an intermediate instruction state is needed. -/
theorem Input.of_disjoint (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (fit : f.addressesFit w (pub 0).val) (resident : f.resident pub m)
    (records : RecordsAt m f.records rs) (count : rs.length = f.count)
    (coords : ∀ r ∈ rs, r.1 < f.dim)
    (valuesFit : ∀ a, (m a).val + incrementAt f.localBase a rs < 2^w)
    (raw : DiagonalTallyBits.WordsAt m f.rawBits xs)
    (num : xs.length = f.teams*f.dim) (lengths : ∀ b ∈ xs, b.length = f.width)
    (recordsDisjoint : separated f.records (2*f.count) f.localBase f.dim)
    (localDir : separated f.localBase f.dim ((pub 0).val+32) 12)
    (claimDir : separated f.claims (f.teams*f.dim) ((pub 0).val+32) 12)
    (rawLocal : separated f.localBase f.dim f.rawBits ((f.teams*f.dim)*f.width))
    (rawClaim : separated f.rawBits ((f.teams*f.dim)*f.width) f.claims (f.teams*f.dim))
    (claimLocal : separated f.localBase f.dim f.claims (f.teams*f.dim))
    (claimBeforeTotal : f.claims+f.dim*f.teams ≤ f.totals) :
    Input f pub m rs xs := by
  let localMem := after f.localBase rs m
  have keep j (hl : (pub 0).val+32 ≤ j) (hu : j < (pub 0).val+44) :
      localMem j = m j :=
    scatter_outside m f.localBase f.dim j rs coords (outside_of_separated localDir hl (by omega))
  have localFrame := resident_congr f pub m localMem resident keep
  refine ⟨fit,resident,records,count,coords,valuesFit,?_,localFrame,?_,num,lengths,rawClaim,?_,
    claimBeforeTotal,claimLocal⟩
  · intro i hi
    exact outside_of_separated recordsDisjoint (Nat.le_add_right ..) (by omega)
  · apply DiagonalTallyBits.words_congr m localMem f.rawBits f.width xs raw lengths
    intro i hl hu
    rw [num] at hu
    exact scatter_outside m _ _ _ rs coords (outside_of_separated rawLocal hl hu)
  · apply resident_congr f pub localMem _ localFrame
    intro j hl hu
    apply DiagonalTallyBits.outputMemory_outside
    rw [num]
    exact outside_of_separated claimDir hl (by omega)

private theorem total_outside (f : TotalsFrame) (a : ℕ → Word w) (m : Memory w) (j len p : ℕ)
    (h : p < f.totals+j ∨ f.totals+(j+len) ≤ p) : writeTotals f a m j len p = m p := by
  induction len generalizing m j with
  | zero => rfl
  | succ len ih =>
    rw [writeTotals,ih _ _ (by omega)]
    exact Function.update_of_ne (by omega) ..

/-- The final bit encoder can use the original directory in every ordinary layout. -/
theorem resultBank_serializeFrame (f : Frame) (g : DiagonalTallyUnpack.Frame) (pub : Arg → Word w)
    (m : Memory w) (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (hi : Input f pub m rs xs) (hg : serializeFrame pub m g f.dim)
    (localDir : separated f.localBase f.dim ((pub 0).val+32) 12)
    (claimDir : separated f.claims (f.teams*f.dim) ((pub 0).val+32) 12)
    (totalDir : separated f.totals f.dim ((pub 0).val+32) 12) :
    serializeFrame pub (resultBank f rs xs m) g f.dim := by
  have he (i : ℕ) (hl : (pub 0).val+32 ≤ i) (hu : i < (pub 0).val+44) :
      resultBank f rs xs m i = m i := by
    have ht := outside_of_separated totalDir hl (by omega : i < (pub 0).val+32+12)
    have hc := outside_of_separated claimDir hl (by omega : i < (pub 0).val+32+12)
    have hh := outside_of_separated localDir hl (by omega : i < (pub 0).val+32+12)
    rw [resultBank,total_outside _ _ _ _ _ _ (by simpa using ht),
      DiagonalTallyBits.outputMemory_outside _ _ _ _ (hi.claimCount ▸ hc)]
    exact scatter_outside m _ _ _ rs hi.coords hh
  dsimp [serializeFrame] at *
  repeat' rw [he _ (by omega) (by omega)]
  exact hg

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
