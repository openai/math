import OAI.Computability.NearSquareRoot.PhysicalWalshBase
import OAI.Computability.NearSquareRoot.PhysicalWalshLaneIndex
import OAI.Computability.NearSquareRoot.BoundedProgramForget
import OAI.Computability.NearSquareRoot.PhysicalWalshPacked

/-! # Two active bits between arbitrary spectator fields

The physical ordinal is `(prefix*4 + digit)*suffixCount + suffix`. Split
its four digit classes, mix the four aligned streams using the exact ±1/2
table, and merge them into the original order. Both spectator rulers and
the precision ruler are preserved for the surrounding driver.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshBase

open IntegerMultiplication Code KernelPassMix PhysicalWalsh PhysicalWalsh.ChildLanes

abbrev Field (P B w : ℕ) := Fin P → Fin 4 → Fin B → Dusk.Grain w

/-- Transform the two middle bits while preserving both spectator indices. -/
def applyField {P B w : ℕ} (x : Field P B w) : Field P B w :=
  fun g j b => transform (fun a => x g a b) j

/-- Original flat physical order on all `P*4*B` records. -/
def flat {P B w : ℕ} (x : Field P B w) : List Dusk.Pair :=
  List.ofFn (fun t : Fin (P*4*B) => Dusk.mark (x t.divNat.divNat t.divNat.modNat t.modNat))

private def blocks {P B w : ℕ} (x : Field P B w) (g : Fin P) (j : Fin 4) :=
  List.ofFn fun b => Dusk.mark (x g j b)

private def lanes {P B w : ℕ} (x : Field P B w) := ChildLanes.rows (List.finRange P) (blocks x)

private theorem streamed {P B w : ℕ} (x : Field P B w) :
    ChildLanes.stream (List.finRange P) (blocks x) = flat x := stream_rect _

private theorem banked {P B w : ℕ} (x : Field P B w) :
    markedBank (List.finRange (P*B)) (fun a j => x a.divNat j a.modNat) = lanes x := by
  unfold lanes blocks
  rw [rows_rect]
  simp [markedBank, MixBankLayout.bank, ← List.ofFn_eq_map]

private theorem laneRuler {P B w : ℕ} (x : Field P B w) :
    ruler ((lanes x).headD []) = tally (P*B) := by
  unfold lanes blocks
  rw [rows_rect, List.ofFn_succ, List.headD_cons]
  simp [ruler,tally,Function.comp_def]

private theorem flat_size {P B w : ℕ} (x : Field P B w) : size (flat x) ≤ P*4*B*(4*(w+1)+4)+1 :=
  PhysicalWalshBank.size_rows_le _ (4*(w+1)+3) (fun _ => (Dusk.volume _).le)

private theorem lanes_size {P B w : ℕ} (x : Field P B w) : size (lanes x) ≤ 4*(P*B*(4*(w+1)+4)+2)+1 :=
  size_rows_rect _ (4*(w+1)+3) (fun _ _ _ => (Dusk.volume _).le)

private abbrev Cuts := Tally × Tally

private def before (z : (Cuts × Tally) × List Dusk.Pair) := ((z.1.1,z.2), z.1.2)
private def after (z : (Cuts × List Dusk.Pair) × Tally) := ((z.1.1, z.2), z.1.2)

private def prepareMix (z : (Cuts × List (List Dusk.Pair)) × Tally) :=
  (((ruler (z.1.2.headD []),z.2),z.1.2),z.1.1)
private def restoreCuts (z : ((Tally × Tally) × List (List Dusk.Pair)) × Cuts) :=
  ((z.2,z.1.2),z.1.1.2)

private theorem before_easy : Easy before := by unfold before; fun_prop
private theorem after_easy : Easy after := by unfold after; fun_prop
private theorem mix_setup : Easy prepareMix := by
  have first : Easy (fun z : (Cuts × List (List Dusk.Pair)) × Tally => z.1.2.headD []) :=
    (Easy.fst.compose Easy.snd).compose (Iter.leader _)
  exact ((first.ruler.pair Easy.snd).pair (Easy.fst.compose Easy.snd)).pair (Easy.fst.compose Easy.fst)
private theorem restore_easy : Easy restoreCuts := by unfold restoreCuts; fun_prop

variable {I : Type} (P B w : I → ℕ) (x : (t : I) → Field (P t) (B t) (w t))

def fieldHeader (t : I) := ((tally (P t), tally (B t)), tally (w t+1))

def fieldVolume (t : I) := (P t+1)*(B t+1)*(w t+1)

private theorem fieldPass (y : (t : I) → Field (P t) (B t) (w t))
    (eq : ∀ t g b, mixMarked coeff (tally (w t+1),List.ofFn (fun j => Dusk.mark (x t g j b))) =
      List.ofFn (fun j => Dusk.mark (y t g j b))) :
    Task (fieldVolume P B w)
      (fun t => send (fieldHeader P B w t, flat (x t)))
      (fun t => send (fieldHeader P B w t, flat (y t))) := by
  let cuts t := (tally (P t), tally (B t))
  let word t := tally (w t+1)
  let n t := tally (P t*B t)
  let l t := List.finRange (P t)
  have lengths (t : I) (g : Fin (P t)) (j : Fin 4) : (blocks (x t) g j).length = B t := List.length_ofFn
  have lengths' (t : I) (g : Fin (P t)) (j : Fin 4) : (blocks (y t) g j).length = B t := List.length_ofFn
  have first := before_easy.on (fun t => (fieldHeader P B w t, flat (x t)))
  have sl := (ChildLanes.splitTask l (fun t => blocks (x t)) B (fun t g _ j => lengths t g j)).forget.left
    (fun t => send (word t))
  simp only [l,List.length_finRange, streamed] at sl
  have setup := mix_setup.on (fun t => ((cuts t,lanes (x t)),word t))
  simp only [prepareMix,laneRuler] at setup
  have mixing := (KernelPassMixBanks.bounded_mixBanks_header ([],[]) ([],[]) (mixMarked coeff)
    (mixMarked_easy coeff) (fun t => List.finRange (P t * B t)) w
    (fun t a j => Dusk.mark (x t a.divNat j a.modNat)) (fun t a j => Dusk.mark (y t a.divNat j a.modNat)) 7
    (fun t a _ j => by rw [Dusk.volume]; omega) (fun t a _ => eq t a.divNat a.modNat)).forget.left
    (fun t => send (cuts t))
  change Task (fun t => ((List.finRange (P t*B t)).length + 1)*(w t+1))
    (fun t => .fork (send ((tally (List.finRange (P t*B t)).length, word t),
      markedBank (List.finRange (P t*B t)) (fun a j => x t a.divNat j a.modNat))) (send (cuts t)))
    (fun t => .fork (send ((tally (List.finRange (P t*B t)).length, word t),
      markedBank (List.finRange (P t*B t)) (fun a j => y t a.divNat j a.modNat))) (send (cuts t))) at mixing
  simp only [List.length_finRange, banked] at mixing
  have back := restore_easy.on (fun t => (((n t,word t),lanes (y t)),cuts t))
  have mg := (ChildLanes.mergeTask l (fun t => blocks (y t)) B (fun t g _ j => lengths' t g j)).forget.left
    (fun t => send (word t))
  simp only [l, List.length_finRange, streamed] at mg
  have last := after_easy.on (fun t => ((cuts t,flat (y t)),word t))
  have chain := (((((first.compose sl).compose setup).compose mixing).compose back).compose mg).compose last
  apply chain.bound 224
  intro t
  have h₁ := flat_size (x t)
  have h₂ := lanes_size (x t)
  have h₃ := flat_size (y t)
  have h₄ := lanes_size (y t)
  change size (fieldHeader P B w t,flat (x t)) + (size (flat (x t))+_) + _ + _ + _ + _ + _ + 1 ≤ _
  simp only [fieldHeader, fieldVolume, cuts, word, n, size_prod,
    size_tally, tally_length]
  have h₅ := h₄
  change size (ChildLanes.rows (List.finRange (P t)) (blocks (y t))) ≤ _ at h₅
  ring_nf at *
  omega

/-- A bounded physical base call at an arbitrary suffix offset, independently
of the lengths of the two spectator fields. -/
theorem fieldTask (h : ∀ t g b, FitsGroup (fun a => x t g a b)) :
    Task (fieldVolume P B w)
      (fun t => send (fieldHeader P B w t, flat (x t)))
      (fun t => send (fieldHeader P B w t, flat (applyField (x t)))) :=
  fieldPass P B w x (fun t => applyField (x t)) fun t g b =>
    mixMarked_exact coeff _ (fun j => divA_fits _ _ _ (h t g b j))

/-- The physical result on every record, including accumulators outside the
range used in the later accuracy proof. -/
def storedBase {P B w : ℕ} (x : Field P B w) : Field P B w :=
  fun g j b => PhysicalWalshGrid.packed (coeff j) (fun a => x g a b)

theorem storedBase_eq {P B w : ℕ} (x : Field P B w) (h : ∀ g b, FitsGroup (fun a => x g a b)) :
    storedBase x = applyField x := by
  funext g j b
  exact PhysicalWalshGrid.packed_eq_rounded _ _ (divA_fits _ _ _ (h g b j))

private theorem boundedPass (y : (t : I) → Field (P t) (B t) (w t))
    (run : Task (fieldVolume P B w) (fun t => send (fieldHeader P B w t,flat (x t)))
      (fun t => send (fieldHeader P B w t,flat (y t)))) :
    Space.BoundedTask (fieldVolume P B w) (fieldVolume P B w)
      (fun t => send (fieldHeader P B w t, flat (x t))) (fun t => send (fieldHeader P B w t,flat (y t))) := by
  apply (Space.BoundedTask.of_time run).bound 1 45
  · simp
  · intro t
    have sz := flat_size (x t)
    change size (fieldHeader P B w t,flat (x t)) + _ + 1 ≤ _
    simp only [fieldHeader,fieldVolume,size_prod,size_tally,tally_length]
    ring_nf at *
    omega

/-- Physical operations and parked data are charged to the same row volume. -/
theorem fieldBounded (h : ∀ t g b, FitsGroup (fun a => x t g a b)) :
    Space.BoundedTask (fieldVolume P B w) (fieldVolume P B w)
      (fun t => send (fieldHeader P B w t, flat (x t)))
      (fun t => send (fieldHeader P B w t, flat (applyField (x t)))) :=
  boundedPass P B w x _ (fieldTask P B w x h)

/-- Unconditional base command for recursion on arbitrary stored arrays. -/
theorem fieldStoredBounded : Space.BoundedTask (fieldVolume P B w) (fieldVolume P B w)
    (fun t => send (fieldHeader P B w t, flat (x t)))
    (fun t => send (fieldHeader P B w t, flat (storedBase (x t)))) :=
  boundedPass P B w x _ (fieldPass P B w x _ fun _ _ _ => PhysicalWalshGrid.packed_eq coeff _)

/-- Natural-number interface to the unconditional leaf, used by the recursive
interpreter. Only indices less than `P*4*B` are serialized. -/
def storedAt {w : ℕ} (B : ℕ) (r : ℕ → Dusk.Grain w) (n : ℕ) : Dusk.Grain w :=
  PhysicalWalshGrid.packed (coeff ⟨n / B % 4, Nat.mod_lt _ (by decide)⟩)
    (fun j => r ((n / B / 4 * 4 + j.val) * B + n % B))

def fromOrdinal {P B w : ℕ} (r : ℕ → Dusk.Grain w) : Field P B w :=
  fun g j b => r ((g.val*4 + j.val)*B + b.val)

private theorem flat_natural {P B w : ℕ} (r : ℕ → Dusk.Grain w) :
    flat (fromOrdinal (P := P) (B := B) r) = (List.range (P*4*B)).map (Dusk.mark ∘ r) := by
  apply List.ext_getElem
  · simp [flat]
  · intro n h₁ h₂
    simp only [flat, List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply]
    change Dusk.mark (r ((n/B/4*4+n/B%4)*B+n%B)) = Dusk.mark (r n)
    rw [Nat.div_add_mod', Nat.div_add_mod']

private theorem stored_natural {P B w : ℕ} (r : ℕ → Dusk.Grain w) :
    flat (storedBase (fromOrdinal (P := P) (B := B) r)) =
      (List.range (P*4*B)).map (Dusk.mark ∘ storedAt B r) := by
  apply List.ext_getElem
  · simp [flat]
  · intro n h₁ h₂
    simp only [flat, List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply]
    rfl

/-- The physically ordered array form of the base transform. The `n`th output
reads its four inputs at fixed suffix and prefix and at all four digit values. -/
theorem ordinalStoredBounded (r : (t : I) → ℕ → Dusk.Grain (w t)) :
    Space.BoundedTask (fieldVolume P B w) (fieldVolume P B w)
      (fun t => send (fieldHeader P B w t,(List.range (P t*4*B t)).map (Dusk.mark ∘ r t)))
      (fun t => send (fieldHeader P B w t,(List.range (P t*4*B t)).map (Dusk.mark ∘ storedAt (B t) (r t)))) := by
  simpa only [stored_natural,flat_natural] using fieldStoredBounded P B w (fun t => fromOrdinal (r t))

end PhysicalWalshBase

end NearSquareRoot
end Computability
end OAI
