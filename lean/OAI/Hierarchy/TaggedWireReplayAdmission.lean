import OAI.Hierarchy.TaggedWirePastPatch

namespace OAI
/-! # Both compared histogram elections are reachable native runs -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.CounterROM
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical
variable {W q d : ℕ} {C : Chart W q d} (R : CounterROM C)
local notation "L" => R.format.windows

theorem replay_admission (P : Effects C) (es : List Event) (initial : Memory W) (raw : Bits (bits R.format.slot es))
    (sep : (L).disjoint es) (forward : (L).ordered C es)
    (dated : es.Pairwise (fun f e=>∀u,(L).inside e u→P.endAt f≤u))
    (own : ∀a,.attempt a∈es→∀i : Fin ((C.layout a).candidates*q),protected C ((R.bank a).base+i.val) (.attempt a))
    (all : ∀input,mounted C es ((L).header es input initial))
    (election : ∀a prior tail m v,es=prior++(.attempt a::tail)→
      run C prior ((L).header es raw initial)=v→ReadBanks.Agree (R.hidden (.attempt a::tail)) m v→
      ready C (.attempt a) m→ ready C (.attempt a) v→R.format.observed a m v) :
    admissible C es ((L).header es raw initial) ↔ ∃!j : Path R.format.slot es initial,encode R.format.slot es initial j=raw := by
  let actualMem:=(L).header es raw initial
  let inv:=fun xs m v=>ReadBanks.Agree (R.hidden xs) m v ∧ ∃prior seed,
    es=prior++xs ∧ run C prior actualMem=v ∧ ReadBanks.Agree (R.hidden es) seed initial ∧ run C prior seed=m
  have whenReady (xs prior : List Event) (seed : Memory W) (split : es=prior++xs)
      (same : ReadBanks.Agree (R.hidden es) seed initial) :
      mounted C prior seed ∧ mounted C xs (run C prior seed) := by
    exact (mounted_append C prior xs seed).mp (split ▸ R.mounted_variant es initial seed all same)
  have trueSeed : ReadBanks.Agree (R.hidden es) actualMem initial :=
    fun u hu=>(R.header_frame es raw initial u hu).symm
  have check : ∀e tail m v,inv (e::tail) m v→
      (accepted C e v ↔ ∃c,(R.format.slot e).word m c=(L).read e v) := by
    rintro (a|b) tail m v ⟨agree,prior,seed,hs,hv,base,hm⟩
    · have left : ready C (.attempt a) m:=hm ▸ (whenReady _ _ _ hs base).2.1
      have right : ready C (.attempt a) v:=hv ▸ (whenReady _ _ _ hs trueSeed).2.1
      exact R.format.native_choice a m v (election a prior tail m v hs hv agree left right) right
        (own a (by simp [hs]))
    · exact ⟨fun _=>⟨(),funext fun i : Fin 0=>Fin.elim0 i⟩,fun _=>trivial⟩
  have advance : ∀e tail m v,inv (e::tail) m v→∀c,(R.format.slot e).word m c=(L).read e v→
      inv tail ((R.format.slot e).next m c) (after C e v) := by
    rintro e tail m v ⟨agree,prior,seed,hs,hv,base,hm⟩ choice word
    let encoded:=(R.format.slot e).word m choice
    let seed':=(L).install e encoded seed
    have base' : ReadBanks.Agree (R.hidden es) seed' initial :=
      R.install_compatible es e (by simp [hs]) encoded seed initial base
    obtain ⟨old,_⟩:=whenReady _ _ _ hs base
    obtain ⟨new,running⟩:=whenReady _ _ _ hs base'
    have pair:=List.pairwise_append.mp (hs ▸ dated)
    have replay : run C prior seed'=R.patch e m choice := by
      exact (R.past_patch P prior e encoded seed (fun f hf=>pair.2.2 f hf e (by simp)) old new).trans
        (congrArg ((L).install e encoded) hm)
    have patched : ready C e (R.patch e m choice):=replay ▸ running.1
    have right : ready C e v:=hv ▸ (whenReady _ _ _ hs trueSeed).2.1
    have afterEq : ReadBanks.Agree (R.hidden tail) ((R.format.slot e).next m choice) (after C e v) := by
      apply R.native_slab_step e tail m v choice agree word (P.endAt e)
      · rintro u ⟨f,hf,range⟩
        exact (List.pairwise_cons.mp pair.2.1).1 f hf u range
      · exact P.read e _ v patched right
      · exact fun u hu=>⟨P.frame e _ patched u hu,P.frame e v right u hu⟩
    refine ⟨afterEq,prior++[e],seed',by simpa using hs,by simp [run_append,hv,run],base',?_⟩
    simp only [run_append,run,replay,R.commit_patch]
  have beginState : inv es initial actualMem :=
    ⟨R.header_frame es raw initial,[],initial,rfl,rfl,fun _ _=>rfl,rfl⟩
  rw [admissible_iff R.format.slot C (L).read inv check advance es initial actualMem beginState,
    (L).chronologically_read es actualMem (all raw) forward,(L).static_header es raw initial sep]

end Hierarchy.WireTelescope.CalendarTape.CounterROM

end
end OAI
