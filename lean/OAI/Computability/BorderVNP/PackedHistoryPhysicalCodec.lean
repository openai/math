import OAI.Computability.BorderVNP.PackedHistoryEquiv
import OAI.Computability.BorderVNP.PackedBankProfiles
import OAI.Computability.BorderVNP.ShortenPhysicalTree

/-! # Fixed public words for the measured physical shortening steps

The guess pins at a stage are addressed by deck tile, relative bin, identity
term and bit position. Given the actual child states, the matched block
counts determine which settings of these pins are valid. Every valid setting
recovers the unique physical summand and the associated successor state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Physical

open Shortening Shortening.Adaptive Packing BankCircuit Crossing Cover VPVNP.VerifierNetwork
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ} {e : PaidIdentity K D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view)

/-- Absolute addresses of the canonical seed bins at this physical round. -/
abbrev Seed (I : Type) {b : ℕ} (B : Fin b → Type) (depth : ℕ → ℕ) (i : Fin b) :=
  (I → Deck (depth (i.val+1)+1)) × B i

/-- The computed number of complete crossing blocks at a seed after the actual
children are combined and their bins are measured. -/
noncomputable def matchedBlocks (i : Fin b) (c : Fin k → A i.val) : Seed I B depth i → ℕ :=
  SeedIntervals.blocks (parallelPacks fun j => (view i.val (c j)).pack).layout
    (F.step i c).bin (F.step i c).perm m

/-- The fixed public word widths fit the matched block count at each physical node. -/
def Fits (w : ℕ → ℕ) : Prop := ∀ i c a, matchedBlocks F i c a < 2^w i.val

/-- Every count fits if the child network's combined cable widths fit. The paper
uses the descriptor and expanded-weight bounds to allocate this binary word. -/
theorem fits_of_widths {w : ℕ → ℕ} (hm : 0 < m) (hw : ∀ (i : Fin b) (c : Fin k → A i.val),
    let p := parallelPacks fun j => (view i.val (c j)).pack
    (∑ z, p.layout.width z) < 2^w i.val) : Fits F w := by
  intro i c a
  let p := parallelPacks fun j => (view i.val (c j)).pack
  have hd := CombiningStep.blocks_le_donor p (F.step i c).bin (F.step i c).perm hm a
  apply hd.trans_lt
  rw [SeedIntervals.count_eq_sum]
  apply lt_of_le_of_lt _ (hw i c)
  exact Finset.sum_le_sum fun z _ => by split <;> first | exact le_rfl | exact Nat.zero_le _

/-- Public relative bin labels, extended by an empty type beyond the prepared stages. -/
def RelativeAt {b : ℕ} (B : Fin b → Type) (j : ℕ) : Type :=
  if h : j < b then B ⟨j,h⟩ else Empty

instance relativeFintype {b : ℕ} (B : Fin b → Type) [∀ i, Fintype (B i)] (j : ℕ) :
    Fintype (RelativeAt B j) := by unfold RelativeAt; split <;> infer_instance

private def relativeEquiv (i : Fin b) : RelativeAt B i.val ≃ B i :=
  Equiv.cast (dite_eq_left i.isLt)

/-- All guess pins of one node, with the count of terms fixed by the paid identity. -/
abbrev Pin (I : Type) {b : ℕ} (B : Fin b → Type) (depth : ℕ → ℕ)
    (terms : ℕ) (w : ℕ → ℕ) (j : ℕ) :=
  ((I → Deck (depth (j+1)+1)) × RelativeAt B j) × Fin terms × Fin (w j)

/-- Static bit address of one physical seed's term-count word. -/
def guessPin (w : ℕ → ℕ) (i : Fin b) (a : Seed I B depth i) (t : Fin e.count)
    (l : Fin (w i.val)) : Pin I B depth e.count w i.val :=
  ((a.1,(relativeEquiv i).symm a.2),t,l)

/-- Physical stage pins and finite-round history pins differ only by the
extension of the relative-bin family outside the prepared depth. -/
def pinEquiv (w : ℕ → ℕ) (i : Fin b) :
    (Seed I B depth i × Fin e.count × Fin (w i.val)) ≃ Pin I B depth e.count w i.val :=
  ((Equiv.refl _).prodCongr (relativeEquiv i).symm).prodCongr (Equiv.refl _)

omit [NeZero D] [Fintype I] [∀ i, Fintype (B i)] in
/-- The history bit addressed by a physical triple is the bit at the actual guess pin. -/
theorem pinEquiv_apply (w : ℕ → ℕ) (i : Fin b) (a : Seed I B depth i)
    (t : Fin e.count) (l : Fin (w i.val)) :
    pinEquiv (e := e) w i (a,t,l) = guessPin (e := e) w i a t l := rfl

/-- Uncurrying the static public pins recovers the exact histogram words
checked by the bank circuit. -/
def fields (w : ℕ → ℕ) (i : Fin b) :
    (Pin I B depth e.count w i.val → Bool) ≃ HistogramBits e (A := Seed I B depth i) (w i.val) where
  toFun x a t l := x (guessPin (e := e) w i a t l)
  invFun x j := x (j.1.1,relativeEquiv i j.1.2) j.2.1 j.2.2
  left_inv x := by funext ⟨⟨a,s⟩,t,l⟩; simp [guessPin]
  right_inv x := by funext ⟨a,s⟩ t l; simp [guessPin]

/-- The exact bijection of the bank guard specializes to the actual dependent
choice type of the physical tree at this child tuple. -/
noncomputable def indices {w : ℕ → ℕ} (hw : Fits F w) (i : Fin b) (c : Fin k → A i.val) :
    {u : HistogramBits e (A := Seed I B depth i) (w i.val) // Accepted e (matchedBlocks F i c) u} ≃
      (F.system.choose i.val i.isLt c).Index :=
  branches e (matchedBlocks F i c) (hw i c)

/-- Encode the physical step's actual histogram choices on fixed, child-independent
pins. This codec can be used directly by the full adaptive tree. -/
noncomputable def codec {w : ℕ → ℕ} (hw : Fits F w) :
    Codec F.system (Pin I B depth e.count w) where
  word j hj c q := (fields (B := B) (depth := depth) (I := I) (e := e) w ⟨j,hj⟩).symm
    ((indices F hw ⟨j,hj⟩ c).symm q).val
  injective j hj c := (fields (B := B) (depth := depth) (I := I) (e := e) w ⟨j,hj⟩).symm.injective.comp
    (Subtype.val_injective.comp (indices F hw ⟨j,hj⟩ c).symm.injective)

/-- The local encoder image is exactly the guard on the *computed* matched
sizes. Thus even invalid guesses and empty seeds have fixed semantics. -/
theorem word_image {w : ℕ → ℕ} (hw : Fits F w) (i : Fin b) (c : Fin k → A i.val)
    (x : Pin I B depth e.count w i.val → Bool) :
    (∃ q, (codec F hw).word i.val i.isLt c q = x) ↔
      Accepted e (matchedBlocks F i c) (fields (e := e) w i x) := by
  let f := fields (I := I) (B := B) (depth := depth) (e := e) w i
  let ix := indices F hw i c
  constructor
  · rintro ⟨q,rfl⟩
    change Accepted e (matchedBlocks F i c) (f (f.symm (ix.symm q).val))
    exact (f.apply_symm_apply _).symm ▸ (ix.symm q).property
  · intro hx
    let u := (⟨f x,hx⟩ : {v // Accepted e (matchedBlocks F i c) v})
    refine ⟨ix u,?_⟩
    change f.symm (ix.symm (ix u)).val = x
    rw [ix.symm_apply_apply]
    exact f.symm_apply_apply x

/-- Feed the matched-size wires and the public guess wires to the physical bank guard.
At each child tuple, simultaneous success of its seed flags is precisely membership
in the local codec's image. The new gates include one real count checker per seed. -/
theorem exists_image_checks {w : ℕ → ℕ} (hw : Fits F w) (i : Fin b)
    {σ : Type*} [Fintype σ] (source : Frame σ (Seed I B depth i × Option (Fin e.count) × Fin (w i.val))) :
    ∃ f : Frame σ (Seed I B depth i),
      f.size ≤ source.size + 1 + Fintype.card (Seed I B depth i) * guardBudget e.count (w i.val) ∧
      ∀ (x : σ → Bool) (c : Fin k → A i.val) (g : Pin I B depth e.count w i.val → Bool),
        (∀ a, ParseBatchSort.value (fun l => source.eval x (a,none,l)) = matchedBlocks F i c a) →
        (∀ a t l, source.eval x (a,some t,l) = fields (e := e) w i g a t l) →
        ((∀ a, f.eval x a = true) ↔ ∃ q, (codec F hw).word i.val i.isLt c q = g) := by
  obtain ⟨f,hs,he⟩ := exists_checks e (w i.val) source
  refine ⟨f,hs,?_⟩
  intro x c g hm hg
  rw [he x, word_image F hw]
  rw [funext hm, funext fun a => funext fun t => funext (hg a t)]

/-- Accepted local words reconstruct the genuine successor pack, including
its tensor, charged wire length, and midpoint concentration. -/
theorem decoded_state {w : ℕ → ℕ} (hw : Fits F w) (i : Fin b) (c : Fin k → A i.val)
    (u : {v : HistogramBits e (A := Seed I B depth i) (w i.val) // Accepted e (matchedBlocks F i c) v}) :
    let q := indices F hw i c u
    let state := view (i.val+1) ((F.system.choose i.val i.isLt c).term q)
    let pack := (F.step i c).result e q
    state.pack.tensor = pack.pack.tensor ∧ state.length = pack.length ∧
      state.concentration = pack.concentration := by
  let q := indices F hw i c u
  exact ⟨funext (F.tensor i c q),F.length i c q,F.concentration i c q⟩

end PackedHistoryCircuit.Physical

end BorderVNP
end Computability
end OAI
