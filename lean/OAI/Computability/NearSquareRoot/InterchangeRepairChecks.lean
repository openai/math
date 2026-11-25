import OAI.Computability.NearSquareRoot.InterchangePayloadBank
import OAI.Computability.NearSquareRoot.InterchangeSpectralMask
import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# The sign-indexed finite repair table in the P192 row bank

The shape descriptor supplies the comparisons of every selected early/late
field pair. These aligned streams accompany the two blocks of check data into
the finite repair lookup.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RepairChecks

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeBank

variable {I A B F E : Type} {X : I → Type} {r : Regime I} {l : I → ℕ} {m : ℕ}

private noncomputable def fullSeries (T : Type) [Fintype T] : Series T :=
  ⟨Finset.univ.toList, Finset.nodup_toList _, fun _ => Finset.mem_toList.mpr (Finset.mem_univ _)⟩

/-- A finite symbol table shared by all addresses and labelled by the computed
sign pattern. The auxiliary sign streams are generated from the descriptor. -/
theorem taggedTable [Fintype A] [Finite F] (points : (i : I) → Series (X i)) (st : Station r points)
    (input : Series A) (out : Series B) (src : F → Tree) (dst : E → Tree)
    (hs : Function.Injective src) (bit : ZMod 2 → F) (read : F → ZMod 2)
    (decode : Function.LeftInverse read bit)
    (tag : (i : I) → X i → SwapRepair.Pattern m)
    (hm : ∀ j, Rip r (fun i => (points i).count) l r.header
      (stackRun points (fun i u => src (bit (tag i u j)))))
    (x : (i : I) → A → X i → F) (τ : SwapRepair.Pattern m → (A → F) → B → E) :
    Drive r (fun i => (points i).count) l (bank points input src x)
      (bank points out dst (fun i b u => τ (tag i u) (fun a => x i a u) b)) := by
  let registers := fullSeries (Fin m ⊕ A)
  let y (i : I) (a : Fin m ⊕ A) (u : X i) := a.elim (fun j => bit (tag i u j)) (fun t => x i t u)
  let lookup (data : (Fin m ⊕ A) → F) := τ (fun j => read (data (.inl j))) (fun a => data (.inr a))
  have alive := bank_alive (l := l) points st input src x
  have copy : Drive r (fun i => (points i).count) l (bank points input src x) (bank points registers src y) := by
    apply Fatigue.dry registers _ (Rip.alivePair (Drive.started st.1) alive)
    rintro (j|a)
    · exact (Drive.fetch st.1 alive).chain (hm j)
    · exact Fatigue.drill input _ (Drive.self st.1 alive) a
  have execute := copy.pipe (table points st registers out src dst hs y lookup)
  have hread (v : ZMod 2) := decode v
  simpa only [lookup, y, Sum.elim_inl, Sum.elim_inr, hread] using execute

private def bitValue [Zero F] [One F] (x : ZMod 2) : F := if x = 0 then 0 else 1

private def readBit [Zero F] [DecidableEq F] (x : F) : ZMod 2 := if x = 0 then 0 else 1

private theorem decodeBit [NonAssocSemiring F] [Nontrivial F] [DecidableEq F] :
    Function.LeftInverse (readBit (F := F)) bitValue := by
  intro x
  have hx : x = 0 ∨ x = 1 := by decide +revert
  rcases hx with rfl | rfl <;> simp [readBit, bitValue]

/-- A numerical pattern agrees with the comparison-mask labels used on tape. -/
private theorem bit_direction [Zero F] [One F] (a b : ℕ) :
    (if InterchangeSpectralStep.direction a b = .gt then (1 : F) else 0) =
      bitValue (if b < a then 1 else 0) := by
  rcases lt_trichotomy a b with h|h|h <;>
    simp [InterchangeSpectralStep.direction, bitValue, h, ne_of_lt, ne_of_gt,
      not_lt_of_gt]

variable {J : Type} {n p : ℕ} [NeZero p]

/-- Read one sign bit from the shape descriptor over every occupied record. -/
private theorem physicalMask [NonAssocSemiring F] (ord : J ≃ Fin n) (P G S : I → Dims.Tape)
    (f : I → ℕ) (hb : 2 ≤ p) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G)
    (ht : Told r S) (slot : J) (src : F → Tree) :
    Rip r (countRows (b:=p) ord P G S f) l r.header
      (stackRun (layoutRows (b:=p) ord P G S f) (fun _ a =>
        src (bitValue (if number (a.2.2.2.1 slot) < number (a.2.1 slot) then 1 else 0)))) := by
  let mark := fun o : Ordering => src (if o = .gt then (1 : F) else 0)
  obtain ⟨k,mask⟩ := SpectralMask.layout_with_setup (b:=p) ord P G S f slot hb hf hp hg ht mark
  let points := layoutRows (b:=p) ord P G S f
  have st := layoutRows_station (b:=p) ord P G S f hb hf hp hg ht
  change Carries _ r.header (stackRun points (fun i a => src (if InterchangeSpectralStep.direction
    (number (a.2.1 slot)) (number (a.2.2.2.1 slot)) = .gt then 1 else 0))) at mask
  simp_rw [bit_direction] at mask
  refine ⟨k,mask.times (unit_mass st.1 k) 2 ?_⟩
  intro i
  have hN : (1 : ℝ) ≤ (points i).count := by exact_mod_cast st.1 i
  have hk : (1 : ℝ) ≤ (r.scale i + 1 : ℝ)^k := one_le_pow₀ (by simp)
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, mass]
  change ((points i).count : ℝ) + (r.scale i + 1 : ℝ)^k ≤ (2 : ℝ) * ((points i).count * ((l i:ℝ) + (r.scale i + 1 : ℝ)^k))
  nlinarith [Nat.cast_nonneg (α:=ℝ) (l i), mul_nonneg (Nat.cast_nonneg (α:=ℝ) (points i).count)
      (Nat.cast_nonneg (α:=ℝ) (l i)), mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hk)]

/-- The complete P192 implementation. A fixed collection of shape-mask scans
and a finite lookup realize any table indexed by the selected physical pairs. -/
theorem physicalTable [Fintype A] [NonAssocSemiring F] [Nontrivial F] [Finite F]
    (ord : J ≃ Fin n) (P G S : I → Dims.Tape) (f : I → ℕ)
    (hb : 2 ≤ p) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (ht : Told r S)
    (slot : Fin m → J) (input : Series A) (out : Series B) (src : F → Tree) (dst : E → Tree)
    (hs : Function.Injective src)
    (x : (i : I) → A → domain (J:=J) (b:=p) P G S f i → F)
    (τ : SwapRepair.Pattern m → (A → F) → B → E) :
    let points := layoutRows (b:=p) ord P G S f
    let tag := fun (i : I) (a : domain (J:=J) (b:=p) P G S f i) (j : Fin m) =>
      if number (a.2.2.2.1 (slot j)) < number (a.2.1 (slot j)) then (1 : ZMod 2) else 0
    Drive r (fun i => (points i).count) l (bank points input src x)
      (bank points out dst (fun i b u => τ (tag i u) (fun a => x i a u) b)) := by
  classical
  intro points tag
  have st := layoutRows_station (b:=p) ord P G S f hb hf hp hg ht
  apply taggedTable points st input out src dst hs bitValue readBit decodeBit tag _ x τ
  intro j
  exact physicalMask ord P G S f hb hf hp hg ht (slot j) src


private theorem broadcastCell [Finite F] {D : I → Type} (payload : (i : I) → Series (D i))
    (src : F → Tree) (hs : Function.Injective src) (sample : (i : I) → D i → F)
    (value : I → F) :
    Carries (fun i => ((payload i).count : ℝ)+1)
      (together (src ∘ value) (stackRun payload fun i d => src (sample i d)))
      (stackRun payload fun i _ => src (value i)) := by
  let w i := ((payload i).count : ℝ)+1
  have erase := interchange_record_table payload sample src (fun _ => send ()) hs
  obtain ⟨M, hM⟩ := (Set.finite_range (fun v => (src v).count)).bddAbove
  have bound (i : I) : ((src (value i)).count : ℝ) ≤ M := by exact_mod_cast hM (Set.mem_range_self _)
  have vm : Volume w (src ∘ value) :=
    ⟨M, fun i => (bound i).trans (le_mul_of_one_le_right (by positivity) (erase.budget i))⟩
  have shape := (Carries.dropLeft erase.budget vm erase.small).chain erase
  have keep := Carries.dropRight erase.budget vm erase.small
  have ruler : Carries w (together (src ∘ value) (stackRun payload fun i d => src (sample i d)))
      (fun i => send (tally (payload i).count)) := by
    convert shape using 1
    funext i
    rw [stackRun, stripe_eq']
    simp [Series.tab, Series.count, tally]
  exact spread payload (src ∘ value) (ruler.twice keep) ⟨M, fun i => by
    dsimp [Function.comp_def, w]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (bound i) (by positivity)⟩

/-- Size the expansion of a per-record mask by reading the delimiters of one
existing packed row. This also covers payloads of length zero. -/
private theorem broadcast [Finite F] {D : I → Type}
    (records : (i : I) → Series (X i)) (st : Station r records)
    (payload : (i : I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (hs : Function.Injective src) (sample : (i : I) → X i × D i → F)
    (value : (i : I) → X i → F) {input : I → Tree}
    (hm : Rip r (fun i => (records i).count) l input (stackRun records fun i a => src (value i a)))
    (ht : Rip r (fun i => (records i).count) l input
      (stackRun records fun i a => stripe (payload i) fun d => src (sample i (a,d)))) :
    Rip r (fun i => (records i).count) l input
      (stackRun records fun i a => stripe (payload i) fun _ => src (value i a)) := by
  obtain ⟨u,hu⟩ := hm
  obtain ⟨v,hv⟩ := ht
  let k := u+v
  have aligned := coalesce records _ _ (hu.larger (mass_le (by dsimp [k]; omega : u ≤ k)))
    (hv.larger (mass_le (by dsimp [k]; omega : v ≤ k)))
  have step := broadcastCell (I := Sigma X) (fun t => payload t.1) src hs
    (fun t d => sample t.1 (t.2,d)) (fun t => value t.1 t.2)
  have scan := liftoff records
    (fun i a => Tree.fork (src (value i a)) (stripe (payload i) (fun d => src (sample i (a,d)))))
    (fun i a => stripe (payload i) (fun _ => src (value i a)))
    (fun i => ((payload i).count : ℝ)+1) step
  refine ⟨k, aligned.chain (scan.times (unit_mass st.1 k) 2 ?_)⟩
  intro i
  have wide : ((records i).count : ℝ)*((payload i).count+1) ≤
      mass r (fun i => (records i).count) l k i := by
    calc
      _ ≤ (records i).count*((l i : ℝ)+1) := by gcongr; exact h i
      _ ≤ _ := by
        simpa [mass] using mass_le (r:=r) (n:=fun i => (records i).count) (l:=l) (Nat.zero_le k) i
  change ((records i).count : ℝ)*((payload i).count+1)+1 ≤ (2 : ℝ) * mass r (fun i => (records i).count) l k i
  linarith [unit_mass (r:=r) (l:=l) st.1 k i]

variable {D : I → Type}

/-- A finite family of per-record masks controls a table at every packed
symbol. Any nonempty physical input bank supplies the common payload shape. -/
theorem payloadTaggedTable [Fintype A] [Nonempty A] [Finite F]
    (records : (i : I) → Series (X i)) (st : Station r records)
    (payload : (i : I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (input : Series A) (out : Series B) (src : F → Tree) (dst : E → Tree)
    (hs : Function.Injective src) (bit : ZMod 2 → F) (read : F → ZMod 2)
    (decode : Function.LeftInverse read bit)
    (tag : (i : I) → X i → SwapRepair.Pattern m)
    (hm : ∀ j, Rip r (fun i => (records i).count) l r.header
      (stackRun records (fun i u => src (bit (tag i u j)))))
    (x : (i : I) → A → X i × D i → F) (τ : SwapRepair.Pattern m → (A → F) → B → E) :
    Drive r (fun i => (records i).count) l (InterchangePayloadBank.render records payload input src x)
      (InterchangePayloadBank.render records payload out dst (fun i b u => τ (tag i u.1) (fun a => x i a u) b)) := by
  let registers := fullSeries (Fin m ⊕ A)
  let y (i : I) (a : Fin m ⊕ A) (u : X i × D i) := a.elim (fun j => bit (tag i u.1 j)) (fun t => x i t u)
  let lookup (data : (Fin m ⊕ A) → F) := τ (fun j => read (data (.inl j))) (fun a => data (.inr a))
  have alive := InterchangePayloadBank.alive records st payload h input src x
  have row (a : A) := Fatigue.drill input (fun i a => stripe (records i) fun z =>
    stripe (payload i) fun d => src (x i a (z,d))) (Drive.self st.1 alive) a
  have copy : Drive r (fun i => (records i).count) l (InterchangePayloadBank.render records payload input src x)
      (InterchangePayloadBank.render records payload registers src y) := by
    apply Fatigue.dry registers _ (Rip.alivePair (Drive.started st.1) alive)
    rintro (j|a)
    · let a := Classical.choice ‹Nonempty A›
      exact broadcast records st payload h src hs (fun i => x i a) (fun i u => bit (tag i u j))
        ((Drive.fetch st.1 alive).chain (hm j)) (row a)
    · exact row a
  have execute := copy.pipe (InterchangePayloadBank.table_nonempty records st payload h
    registers out src dst hs y lookup)
  have hread (v : ZMod 2) := decode v
  simpa only [lookup, y, Sum.elim_inl, Sum.elim_inr, hread] using execute

/-- The lookup on packed payloads from actual shape descriptors and physical
field selections. All payload positions in a record share its spectral sign. -/
theorem physicalPayloadTable [Fintype A] [Nonempty A] [NonAssocSemiring F] [Nontrivial F] [Finite F]
    (ord : J ≃ Fin n) (P G S : I → Dims.Tape) (f : I → ℕ)
    (hb : 2 ≤ p) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (ht : Told r S)
    (payload : (i : I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (slot : Fin m → J) (input : Series A) (out : Series B) (src : F → Tree) (dst : E → Tree)
    (hs : Function.Injective src) (x : (i : I) → A → domain (J:=J) (b:=p) P G S f i × D i → F)
    (τ : SwapRepair.Pattern m → (A → F) → B → E) :
    let points := layoutRows (b:=p) ord P G S f
    let tag := fun (i : I) (a : domain (J:=J) (b:=p) P G S f i) (j : Fin m) =>
      if number (a.2.2.2.1 (slot j)) < number (a.2.1 (slot j)) then (1 : ZMod 2) else 0
    Drive r (fun i => (points i).count) l (InterchangePayloadBank.render points payload input src x)
      (InterchangePayloadBank.render points payload out dst (fun i b u => τ (tag i u.1) (fun a => x i a u) b)) := by
  classical
  intro points tag
  have st := layoutRows_station (b:=p) ord P G S f hb hf hp hg ht
  apply payloadTaggedTable points st payload h input out src dst hs bitValue readBit decodeBit tag _ x τ
  intro j
  exact physicalMask ord P G S f hb hf hp hg ht (slot j) src

end Interchange.RepairChecks

end NearSquareRoot
end Computability
end OAI
