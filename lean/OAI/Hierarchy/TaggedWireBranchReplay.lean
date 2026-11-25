import OAI.Hierarchy.TaggedWireEncodedExecution
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # The exact native prefix of every complete continuation of a signed path -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical

/-- Append the actual remaining choices to the ones already made. -/
def Prefix.withSuffix {X : Type} {slots : Event→Slot X} {es : List Event} {initial : X} :
    ∀{tail x},Prefix slots es initial tail x→Path slots tail x→Path slots es initial
  | _,_,.start,j=>j
  | _,_,.advance t c,j=>t.withSuffix ⟨c,j⟩

namespace CounterROM
variable {W q d : ℕ} {C : Chart W q d} (R : CounterROM C) (P : Effects C)
local notation "L" => R.format.windows
local notation "slots" => R.format.slot
variable (es : List Event) (initial : Memory W) (sep : R.format.windows.disjoint es)
    (dated : es.Pairwise (fun f e=>∀u,R.format.windows.inside e u→P.endAt f≤u))
    (all : ∀b : Bits (bits R.format.slot es),mounted C es (R.format.windows.header es b initial))

include sep dated all in
/-- A physically runnable completed tape agrees with the semantic prefix on
all words other than the still-unread private pages. Its remaining immutable
words are precisely the specified suffix, including the next ballot. -/
theorem replay_suffix {tail x} (t : Prefix slots es initial tail x) (j : Path slots tail x) :
    let raw:=encode slots es initial (t.withSuffix j)
    let seed:=(L).header es raw initial
    ∃prior, es=prior++tail ∧
      ReadBanks.Agree (R.hidden tail) x (run C prior seed) ∧
      encode slots tail x j=actual slots C (L).read tail (run C prior seed) := by
  induction t with
  | start=>
    refine ⟨[],rfl,R.header_frame es (encode slots es initial j) initial,?_⟩
    let b:=encode slots es initial j
    change b=actual slots C (L).read es ((L).header es b initial)
    rw [R.future_words P es _ (all b) dated]
    exact ((L).static_header es b initial sep).symm
  | @advance e tail x t choice ih=>
    let old : Path slots (e::tail) x:=⟨choice,j⟩
    let raw:=encode slots es initial (t.withSuffix old)
    let seed:=(L).header es raw initial
    obtain ⟨past,eq,agree,words⟩:=ih old
    let actualState:=run C past seed
    obtain ⟨head,suffix⟩:=R.matched_cons_words e tail x actualState old words
    have right:=((mounted_append C past (e::tail) seed).mp (eq ▸ all raw)).2.1
    let current:=R.original_input P es initial dated all t
    let patched:=current.patch R P es initial dated all choice
    have left:=(patched.resident R es initial all).1
    have pair:=(List.pairwise_append.mp (eq ▸ dated)).2.1
    have next : ReadBanks.Agree (R.hidden tail) ((slots e).next x choice) (after C e actualState):=by
      apply R.native_slab_step e tail x actualState choice agree head (P.endAt e)
      · rintro u ⟨s,h,range⟩
        exact (List.pairwise_cons.mp pair).1 s h u range
      · exact P.read e _ _ left right
      · exact fun u hi=>⟨P.frame e _ left u hi,P.frame e _ right u hi⟩
    refine ⟨past++[e],by simpa using eq,?_,?_⟩
    · simpa only [Prefix.withSuffix,run_append,run] using next
    · simpa only [Prefix.withSuffix,run_append,run] using suffix

include sep dated all in
/-- The actual current native page in a completed run is exactly the patch
of the semantic state, up to *strictly future* private memory. -/
theorem replay_choice {e tail x} (t : Prefix slots es initial (e::tail) x)
    (c : (slots e).choice x) (next : Path slots tail ((slots e).next x c))
    (scheduled : events C.mesh=es := by rfl) :
    let j : Path slots es initial:=t.withSuffix ⟨c,next⟩
    let seed:=(L).header es (encode slots es initial j) initial
    ∃prior,Calendar.Slot C seed e prior tail (run C prior seed) ∧
      ReadBanks.Agree (R.hidden tail) (R.patch e x c) (run C prior seed) := by
  let j : Path slots es initial:=t.withSuffix ⟨c,next⟩
  let raw:=encode slots es initial j
  let seed:=(L).header es raw initial
  obtain ⟨prior,eq,agree,words⟩:=R.replay_suffix P es initial sep dated all t ⟨c,next⟩
  have head:=(R.matched_cons_words e tail x (run C prior seed) ⟨c,next⟩ words).1
  have complete : mounted C (events C.mesh) seed := scheduled.symm ▸ all raw
  exact ⟨prior,slot_of_split C seed e prior tail _ (scheduled.trans eq) rfl complete,
    R.patch_agrees e tail x _ c agree head⟩

end CounterROM
end Hierarchy.WireTelescope.CalendarTape
end

end OAI
