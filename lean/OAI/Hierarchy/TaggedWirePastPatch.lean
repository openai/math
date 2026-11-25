import OAI.Hierarchy.TaggedWireChronologicalTape
import OAI.Hierarchy.TaggedWireHeaderRestore

namespace OAI
/-! # A later selector word can be installed before replaying the original calendar prefix -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.CounterROM
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical
variable {W q d : ℕ} {C : Chart W q d} (R : CounterROM C)
local notation "L" => R.format.windows

/-- The cutoff and all native effects belong to the earlier event. -/
structure Effects (C : Chart W q d) where
  endAt : Event→ℕ
  read : ∀ e m m',ready C e m→ ready C e m'→
    (∀u,u<endAt e→m u=m' u)→∀u,u<endAt e→after C e m u=after C e m' u
  frame : ∀ e m,ready C e m→∀u,endAt e≤u→after C e m u=m u

theorem past_patch (P : Effects C) (earlier : List Event) (e : Event) (word : Bits (R.format.slot e).bits)
    (m : Memory W) (later : ∀f∈earlier,∀u,(L).inside e u→P.endAt f≤u)
    (first : mounted C earlier m) (second : mounted C earlier ((L).install e word m)) :
    run C earlier ((L).install e word m)=(L).install e word (run C earlier m) := by
  induction earlier generalizing m with
  | nil=>rfl
  | cons f fs ih=>
    have commute : after C f ((L).install e word m)=(L).install e word (after C f m) := by
      funext u
      by_cases small:u<P.endAt f
      · have below : ∀x,x<P.endAt f→¬(L).inside e x :=
          fun x hx here=>Nat.not_le_of_gt hx (later f (List.mem_cons_self ..) x here)
        rw [(L).install_off _ _ _ u (below u small)]
        exact P.read _ _ _ second.1 first.1 (fun x hx=>(L).install_off _ _ _ x (below x hx)) u small
      · rw [P.frame f _ second.1 u (Nat.le_of_not_gt small)]
        by_cases here:(L).inside e u
        · exact (L).install_on _ _ _ _ u here
        · rw [(L).install_off _ _ _ u here,(L).install_off _ _ _ u here,P.frame f _ first.1 u (Nat.le_of_not_gt small)]
    change run C fs (after C f ((L).install e word m))=(L).install e word (run C fs (after C f m))
    rw [commute]
    exact ih _ (fun u hu=>later u (List.mem_cons_of_mem _ hu)) first.2 (commute ▸ second.2)

theorem install_compatible (es : List Event) (e : Event) (present : e∈es)
    (word : Bits (R.format.slot e).bits) (m initial : Memory W)
    (orig : ReadBanks.Agree (R.hidden es) m initial) :
    ReadBanks.Agree (R.hidden es) ((L).install e word m) initial := by
  intro u off
  rw [(L).install_off _ _ _ u (fun h=>off ⟨e,present,h⟩)]
  exact orig _ off

/-- Providing a mounted run on every raw bit tape gives one on every possible
word-page replacement, including words at which the admission test returns false. -/
theorem mounted_variant (es : List Event) (init m : Memory W)
    (all : ∀raw,mounted C es ((L).header es raw init)) (orig : ReadBanks.Agree (R.hidden es) m init) :
    mounted C es m := by
  have h:=(L).header_restore es m init orig
  rw [←h]
  exact all _

end Hierarchy.WireTelescope.CalendarTape.CounterROM

end
end OAI
