import OAI.Hierarchy.TaggedWireReachedInput
import OAI.Hierarchy.TaggedWireChronologicalTape

namespace OAI
/-! # Exact final RAM of a signed semantic path on its own original bits -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.CounterROM
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical
variable {W q d : ℕ} {C : Chart W q d} (R : CounterROM C) (P : Effects C)
local notation "L" => R.format.windows
local notation "slots" => R.format.slot

theorem matched_cons_words (e : Event) (tail : List Event) (m x : Memory W)
    (j : Path slots (e::tail) m) (same : encode slots (e::tail) m j=actual slots C (L).read (e::tail) x) :
    (slots e).word m j.1=(L).read e x ∧
      encode slots tail ((slots e).next m j.1) j.2=actual slots C (L).read tail (after C e x) := by
  change (Fin.addCases ((slots e).word m j.1) (encode slots tail ((slots e).next m j.1) j.2) :
      Bits ((slots e).bits+bits slots tail)) =
    Fin.addCases ((L).read e x) (actual slots C (L).read tail (after C e x)) at same
  constructor <;> funext i
  · simpa only [Fin.addCases_left] using congrFun same (Fin.castAdd (bits slots tail) i)
  · simpa only [Fin.addCases_right] using congrFun same (Fin.natAdd (slots e).bits i)

theorem future_words (tail : List Event) (m : Memory W) (good : mounted C tail m)
      (later : tail.Pairwise (fun f e=>∀u,(L).inside e u→P.endAt f≤u)) :
      actual slots C (L).read tail m=(L).static tail m := by
  induction tail generalizing m with
  | nil=>rfl
  | cons e tail ih=>
    have keep : (L).agrees tail (after C e m) m:=by
      intro t ht i
      apply P.frame e m good.1
      apply (List.pairwise_cons.mp later).1 t ht
      exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left i.isLt _⟩
    change (Fin.addCases ((L).read e m) (actual slots C (L).read tail (after C e m)) :
      Bits ((slots e).bits+bits slots tail))=(L).static (e::tail) m
    rw [ih _ good.2 (List.pairwise_cons.mp later).2,(L).static_congr tail keep]
    rfl

/-- Reading the authenticated choice words in event order reproduces the
entire execution, including every mutable control word at the final date. -/
theorem terminal_encoded (es : List Event) (initial : Memory W)
    (sep : (L).disjoint es)
    (dated : es.Pairwise (fun f e=>∀u,(L).inside e u→P.endAt f≤u))
    (all : ∀b,mounted C es ((L).header es b initial)) (j : Path slots es initial) :
    terminal slots es initial j=run C es ((L).header es (encode slots es initial j) initial) := by
  have tracking (tail : List Event) (m : Memory W) (T : OnTape R es tail initial m) (x : Memory W)
      (readyAll : mounted C tail x) (agree : ReadBanks.Agree (R.hidden tail) m x)
      (j : Path slots tail m) (agreeWords : encode slots tail m j=actual slots C (L).read tail x) :
      terminal slots tail m j=run C tail x := by
    induction tail generalizing m x with
    | nil =>
      apply funext
      intro a
      exact agree a (by simp [hidden])
    | cons e tail ih =>
      let c:=j.1
      obtain ⟨head,rest⟩:=R.matched_cons_words e tail m x j agreeWords
      let recorded:=T.patch R P es initial dated all c
      have good:=recorded.resident R es initial all
      have following : OnTape R es tail initial ((slots e).next m c) :=
        ⟨recorded.prior++[e],by simpa using recorded.split,recorded.bits,by
          simp only [run_append,run,recorded.state,R.commit_patch]⟩
      have pair:=(List.pairwise_append.mp (T.split ▸ dated)).2.1
      have same : ReadBanks.Agree (R.hidden tail) ((slots e).next m c) (after C e x):=by
        apply R.native_slab_step e tail m x c agree head (P.endAt e)
        · rintro u ⟨s,h,range⟩
          exact (List.pairwise_cons.mp pair).1 s h u range
        · exact P.read e _ _ good.1 readyAll.1
        · intro u hi
          exact ⟨P.frame e _ good.1 u hi,P.frame e _ readyAll.1 u hi⟩
      exact ih _ following _ readyAll.2 same j.2 rest
  let raw:=encode slots es initial j
  let term:=(L).header es raw initial
  have start : OnTape R es es initial initial:=⟨[],rfl,(L).static es initial,(L).header_restore es _ _ (fun _ _=>rfl)⟩
  exact tracking es initial start term (all raw) (R.header_frame es raw initial) j
    (by rw [R.future_words P es term (all raw) dated];exact ((L).static_header es raw initial sep).symm)

end Hierarchy.WireTelescope.CalendarTape.CounterROM
end

end OAI
