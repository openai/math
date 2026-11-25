import OAI.Hierarchy.TaggedWireReplayAdmission
import OAI.Hierarchy.TaggedWireReachable

namespace OAI
/-! # The original full private input realizing each reachable physical state -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.CounterROM
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {W q d : ℕ} {C : Chart W q d} (R : CounterROM C)
local notation "L" => R.format.windows

structure OnTape (events tail : List Event) (initial current : Memory W) where
  prior : List Event
  split : events=prior++tail
  bits : Bits (CalendarTape.bits R.format.slot events)
  state : run C prior ((L).header events bits initial)=current

variable (P : Effects C) (es : List Event) (initial : Memory W)

/-- Replace this event's exact native choice in the *initial* tape. Earlier
word writes then reconstruct exactly the patched intermediate memory. -/
def OnTape.patch
    (dated : es.Pairwise (fun f e=>∀u,R.format.windows.inside e u→P.endAt f≤u))
    (all : ∀raw : Bits (CalendarTape.bits R.format.slot es),mounted C es (R.format.windows.header es raw initial))
    {e : Event} {tail : List Event} {m : Memory W}
    (T : OnTape R es (e::tail) initial m) (c : (R.format.slot e).choice m) :
    OnTape R es (e::tail) initial (R.patch e m c) := by
  let seed:=(L).header es T.bits initial
  let word:=(R.format.slot e).word m c
  let patched:=(L).install e word seed
  have same : ReadBanks.Agree (R.hidden es) seed initial := fun u hu=>(R.header_frame es T.bits initial u hu).symm
  have compat := R.install_compatible es e (by rw [T.split]; simp) word seed initial same
  have restore : (L).header es ((L).static es patched) initial=patched:=(L).header_restore es patched initial compat
  have left:=(mounted_append C T.prior (e::tail) seed).mp (T.split ▸ all T.bits)
  have right:=(mounted_append C T.prior (e::tail) patched).mp (T.split ▸ R.mounted_variant es initial patched all compat)
  have before:=List.pairwise_append.mp (T.split ▸ dated)
  refine ⟨T.prior,T.split,(L).static es patched,?_⟩
  rw [restore]
  exact (R.past_patch P T.prior e word seed (fun f hf=>before.2.2 f hf e (by simp)) left.1 right.1).trans
    (congrArg ((L).install e word) T.state)

def original_input
    (dated : es.Pairwise (fun f e=>∀u,R.format.windows.inside e u→P.endAt f≤u))
    (all : ∀raw : Bits (CalendarTape.bits R.format.slot es),mounted C es (R.format.windows.header es raw initial))
    {tail : List Event} {m : Memory W} (h : Prefix R.format.slot es initial tail m) : OnTape R es tail initial m := by
  induction h with
  | start =>
    exact ⟨[],rfl,(L).static es initial,(L).header_restore es _ _ (fun _ _=>rfl)⟩
  | @advance e tail m old choice prev =>
    let pre:=prev.patch R P es initial dated all choice
    refine ⟨pre.prior++[e],by simpa using pre.split,pre.bits,?_⟩
    simp only [run_append,run,pre.state,R.commit_patch]

theorem OnTape.resident
    (all : ∀raw : Bits (CalendarTape.bits R.format.slot es),mounted C es (R.format.windows.header es raw initial))
    {tail : List Event} {m : Memory W} (T : OnTape R es tail initial m) : mounted C tail m :=
  T.state ▸ ((mounted_append C T.prior tail _).mp (T.split ▸ all T.bits)).2

end Hierarchy.WireTelescope.CalendarTape.CounterROM

end
end OAI
