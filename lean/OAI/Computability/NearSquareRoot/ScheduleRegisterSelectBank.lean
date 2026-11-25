import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectMix
import OAI.Computability.NearSquareRoot.ScheduleRegisterMapping
import OAI.Computability.NearSquareRoot.KernelPassMixPhysical

/-! # A common register bank for the physical dyadic mixing pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterSelect
open IntegerMultiplication Code KernelPass KernelPassMix MixBankLayout Filter
open RegisterWitness (Timed Bounded)
local notation "RE" => RegisterWitness.Easy
private abbrev Record := Dusk.Pair
private abbrev zero : Record := ([],[])

theorem preserveHeader {I : Type*} {R : ℕ} (hR : 3 ≤ R) (header body reply : I → Tree) (budget : I → ℕ)
    (h : Timed R budget (fun t => .fork (header t) (body t)) reply) :
    Timed R (fun t => (header t).count + budget t) (fun t => .fork (header t) (body t))
      (fun t => .fork (header t) (reply t)) :=
  register_witness R from KernelPassMixBanks.preserveHeader header body reply budget (RegisterWitness.forget h)

open private tail_easy from OAI.Computability.NearSquareRoot.KernelPassMixBankLayout

private theorem align_all : ∀ᶠ R in atTop, ∀ i, RE R (align i zero) := by
  have zeroLeaf : Code.Easy (align 0 zero) := easy_align 0 zero
  have tail : Code.Easy (fun p : Tally × List (List Record) => (p.1,p.2.tail)) :=
    Code.Easy.fst.pair (Code.Easy.snd.compose tail_easy)
  have head : Code.Easy (fun p : Tally × List (List Record) => p.2.headD []) :=
    Code.Easy.snd.compose (Iter.leader [])
  filter_upwards [eventually_ge_atTop 4, easy_eventually zeroLeaf, easy_eventually tail, easy_eventually head,
    easy_eventually (easy_zip zero ([] : List Record)), easy_eventually (Code.Easy.cons (X := Record)).mapping]
    with R hR hBase ht hh hz hc
  intro i
  induction i with
  | zero => exact hBase
  | succ i ih => exact ((RegisterWitness.Easy.pair (by omega) hh (ht.compose ih)).compose hz).compose hc

private theorem scatter_all : ∀ᶠ R in atTop, ∀ o, RE R (scatter o zero) := by
  have tail : Code.Easy (@List.tail Record) := by
    have h := Code.Easy.listCase ([] : List Record) (Code.Easy.snd : Code.Easy (fun p : Record × List Record => p.2))
    convert h using 1
    funext l
    cases l <;> rfl
  filter_upwards [eventually_ge_atTop 4,easy_eventually (Iter.leader zero).mapping, easy_eventually tail.mapping]
    with R hR hh ht
  intro o
  induction o with
  | zero => exact RegisterWitness.Easy.const (by omega) _
  | succ o ih => exact (RegisterWitness.Easy.pair (by omega) hh (ht.compose ih)).compose RegisterWitness.Easy.cons

open private finish finish_eq size_replicate from OAI.Computability.NearSquareRoot.KernelPassMixBanks

private theorem finish_all : ∀ᶠ R in atTop, ∀ i o (c : Fin o → Fin i → Coefficient),
    RE R (finish i o zero zero (KernelPassMix.mixMarked c)) := by
  have shape : Code.Easy (fun r : List Tally × List (List Record) => (ruler r.1,r.2)) := by fun_prop
  filter_upwards [eventually_ge_atTop 4, align_all, scatter_all, mixMarked, easy_eventually shape,
    easy_eventually (easy_zip ([] : Tally) ([] : List Record))] with R hR align scatter mix shape zip
  intro i o c
  exact ((RegisterWitness.Easy.pair (by omega) (RegisterWitness.Easy.fst hR)
    (shape.compose (align i))).compose zip |>.compose (RegisterWitness.Easy.mapping hR (mix i o c))).compose (scatter o)

/-- All matrix dimensions share one register cutoff. For arbitrary address
and width families the selected command satisfies the original bounded-space
P192 contract, transports the two rulers, and writes the prescribed marked records. -/
theorem mixBanks_exact : ∀ᶠ R in atTop, ∀ (i o : ℕ) (c : Fin o → Fin i → Coefficient)
    {J : Type} {β : J → Type} (l : (t : J) → List (β t)) (w : J → ℕ)
    (x : (t : J) → β t → Fin i → Dusk.Grain (w t)) (y : (t : J) → β t → Fin o → Dusk.Grain (w t)),
    (∀ t, ∀ a ∈ l t, KernelPassMix.mixMarked c (tally (w t+1),List.ofFn (fun j => Dusk.mark (x t a j))) =
      List.ofFn (fun b => Dusk.mark (y t a b))) →
    Bounded R (fun t => ((l t).length + 1) * (w t + 1)) (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length,tally (w t + 1)),markedBank (l t) (x t)))
      (fun t => send ((tally (l t).length,tally (w t + 1)),
        markedBank (l t) (y t))) := by
  filter_upwards [eventually_ge_atTop 4, finish_all, checked_eventually (generate (X := Tally))] with
    R hR hfinish hgen
  intro i o c J β l w x y correct
  let rulers (t : J) := List.replicate (l t).length (tally (w t+1))
  let h (t : J) := send (tally (l t).length,tally (w t+1))
  let src (t : J) := markedBank (l t) (x t)
  let out (t : J) := markedBank (l t) (y t)
  let budget (t : J) := ((l t).length+1)*(w t+1)
  have gen := Timed.on hgen (fun t => (tally (l t).length,tally (w t+1)))
  have withBank := register_witness R from Task.left (RegisterWitness.forget gen) (fun t => send (src t))
  have run := Timed.on (hfinish i o c) (fun t => (rulers t,src t))
  have done (t : J) : finish i o zero zero (KernelPassMix.mixMarked c) (rulers t,src t) = out t :=
    finish_eq zero zero _ _ (l t) _ _ (correct t)
  have base : Timed R budget (fun t => .fork (h t) (send (src t))) (fun t => send (out t)) := by
    dsimp [Function.comp_def] at withBank run
    simp only [tally_length] at withBank
    simp only [done] at run
    apply (Timed.compose withBank run).bound (i*10+12)
    intro t
    have sz := size_bank_le (l t) (fun a j => Dusk.mark (x t a j)) (7*(w t+1))
      (fun a _ j => by rw [Dusk.volume]; omega)
    simp only [rulers,src,markedBank,size_replicate,size_tally,tally_length,budget]
    ring_nf at sz ⊢
    omega
  have header := preserveHeader (by omega) h (fun t => send (src t)) (fun t => send (out t)) budget base
  have cap := RegisterWitness.Bounded.of_time header
  apply cap.bound 10 (i*10+25)
  · intro t
    change size (tally (l t).length,tally (w t+1)) + budget t + 1 ≤ _
    simp only [size_prod,size_tally,tally_length,budget]
    ring_nf
    omega
  · intro t
    have sz := size_bank_le (l t) (fun a j => Dusk.mark (x t a j)) (7*(w t+1))
      (fun a _ j => by rw [Dusk.volume]; omega)
    change size ((tally (l t).length,tally (w t+1)),src t) +
      (size (tally (l t).length,tally (w t+1)) + budget t) + 1 ≤ _
    simp only [src,markedBank,size_prod,size_tally,tally_length,budget]
    ring_nf at sz ⊢
    omega

/-- All matrix dimensions share one register cutoff. For arbitrary address
and width families the selected command satisfies the original bounded-space
P192 contract, transports the two rulers, and writes the rounded mix. -/
theorem mixBanks : ∀ᶠ R in atTop, ∀ (i o : ℕ) (c : Fin o → Fin i → Coefficient)
    {J : Type} {β : J → Type} (l : (t : J) → List (β t)) (w : J → ℕ)
    (x : (t : J) → β t → Fin i → Dusk.Grain (w t)),
    (∀ t, ∀ a ∈ l t, ∀ b, Grid.focus (w t) (Grid.divA (denom (c b)) (accum (c b) (Grid.aspect ∘ x t a)))) →
    Bounded R (fun t => ((l t).length + 1) * (w t + 1)) (fun t => ((l t).length + 1) * (w t + 1))
      (fun t => send ((tally (l t).length,tally (w t + 1)),markedBank (l t) (x t)))
      (fun t => send ((tally (l t).length,tally (w t + 1)),
        markedBank (l t) (fun a b => rounded (c b) (x t a)))) := by
  filter_upwards [mixBanks_exact] with R run
  intro i o c J β l w x room
  exact run i o c l w x _ (fun t a ha => mixMarked_exact c (x t a) (room t a ha))

end RegisterSelect

end NearSquareRoot
end Computability
end OAI
