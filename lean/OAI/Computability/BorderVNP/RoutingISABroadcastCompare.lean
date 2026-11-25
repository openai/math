import OAI.Computability.BorderVNP.RoutingISABroadcastCompareBit
import OAI.Computability.BorderVNP.RoutingISACheckLoop

/-! # Native comparisons of the entire incident broadcast prefix

The inner scan reads every bit of a partner and tests it against the saved reference.
The outer scan skips precisely the caller's own team. Both scans preserve memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {m : Memory w}

private theorem mem_eq_of_readings {m' : Memory w} (h : readings m' = readings m) : m' = m :=
  funext fun j => Fin.ext (congrFun h j)

private theorem comparePartner (f : BroadcastFrame)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val) :
    PartnerCheck pub macros m f.teams f.team (2 + f.header*(compareHeaderBit.slots+1))
      (.seq (.copy 10 0) (.whileLt 10 6 compareHeaderBit)) (fun s => f.Stable (readings s))
      (fun i => ∀ j < f.header, m (f.addr i j) = m (f.dst+j)) := by
  suffices all : ∀ i < f.teams, i ≠ f.team → ∀ s : Bank w, f.Stable (readings s) →
      (s 11).val = i →
      TestRun pub macros (.seq (.copy 10 0) (.whileLt 10 6 compareHeaderBit)) s m
        (2 + f.header*(compareHeaderBit.slots+1))
        (∀ j < f.header, m (f.addr i j) = m (f.dst+j))
        (fun z => f.Stable z.reg ∧ z.reg 11 = i ∧ z.mem = readings m) by
    constructor
    · intro i hi other s hs pos good
      obtain ⟨es,t,mt,r,c,st,ti,tm⟩ := (all i hi other s hs pos).complete good
      obtain rfl := mem_eq_of_readings tm
      exact ⟨es,t,r,c,st,Fin.ext (ti.trans pos.symm)⟩
    · intro i hi other s hs pos es t mt run
      obtain ⟨good,st,ti,tm⟩ := (all i hi other s hs pos).sound run
      exact ⟨mem_eq_of_readings tm,st,Fin.ext (ti.trans pos.symm),good⟩
  intro i hi other s hs pos
  let ok (j : ℕ) := m (f.addr i j) = m (f.dst+j)
  let Inv (j : ℕ) (z : NatState) := f.Stable z.reg ∧ z.reg 11 = i ∧ z.reg 10 = j ∧ z.mem = readings m
  have step : ∀ j < f.header, ∀ t mt, Inv j (.ofWords t mt) →
      TestRun pub macros compareHeaderBit t mt compareHeaderBit.slots (ok j) (Inv (j+1)) := by
    rintro j hj t mt ⟨st,hp,hj',hm⟩
    have eqm : mt = m := mem_eq_of_readings hm
    subst mt
    change (t 11).val = i at hp
    change (t 10).val = j at hj'
    obtain ⟨u,stable,part,next,forward,sound⟩ := compareHeaderBit_paths (macros := macros)
      f image fit st (hp ▸ hi) (hp ▸ other) (hj' ▸ hj)
    have post : Inv (j+1) (.ofWords u m) :=
      ⟨stable,(congrArg Fin.val part).trans hp,next.trans (congrArg (· + 1) hj'),rfl⟩
    constructor
    · intro check
      obtain ⟨es,r,c⟩ := forward (by simpa only [hp,hj'] using check)
      exact ⟨es,u,m,r,c,post⟩
    · intro es v mv run
      obtain ⟨rfl,rfl,eq⟩ := sound run
      exact ⟨by simpa only [hp,hj'] using eq,post⟩
  let u := Function.update s 10 (s 0)
  have start : Runs pub macros (.copy 10 0) s m [tick w] u m := .localStep m rfl rfl
  have inv : Inv 0 (.ofWords u m) := by
    refine ⟨?_,?_,?_,rfl⟩
    · simpa (config := {decide := true}) [BroadcastFrame.Stable,NatState.ofWords,readings,u] using hs
    · simpa (config := {decide := true}) [NatState.ofWords,readings,u] using pos
    · simpa [NatState.ofWords,readings,u] using hs.1
  have chk := test_counted_loop 10 6 compareHeaderBit f.header (fun _ => compareHeaderBit.slots)
    ok Inv (fun _ _ h => ⟨h.2.2.1,h.1.2.2.2.2.2.2.1⟩) step 0 (Nat.zero_le _) u m inv
  constructor
  · intro good
    obtain ⟨es,t,mt,r,c,st,hp,_,hm⟩ := chk.complete (fun j _ hj => good j hj)
    refine ⟨_,t,mt,start.seq r,?_,st,hp,hm⟩
    change 1 + traceCost es ≤ _
    have bound : traceCost es ≤ f.header*(compareHeaderBit.slots+1)+1 := by
      simpa [Finset.sum_const] using c
    omega
  · intro es t mt run
    obtain ⟨u',mu,_,_,_,first,loop⟩ := Runs.seq_iff.mp run
    obtain ⟨_,rfl,rfl⟩ := first.unique_of_deterministic rfl start
    obtain ⟨pass,st,hp,_,hm⟩ := chk.sound loop
    exact ⟨fun j hj => pass j (Nat.zero_le _) hj,st,hp,hm⟩

private theorem stablePartner (f : BroadcastFrame) :
    PartnerRegs f.teams f.team (fun s : Bank w => f.Stable (readings s)) where
  values _ h := ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩
  counter s hs v := by
    simpa (config := {decide := true}) [BroadcastFrame.Stable, readings] using hs

private theorem partnerStart {s : Bank w} (f : BroadcastFrame) (hs : f.Stable (readings s)) :
    ∃ u, Runs pub macros (.copy 11 0) s m [tick w] u m ∧ f.Stable (readings u) ∧ (u 11).val = 0 :=
  ⟨_,Runs.localStep m rfl rfl,(stablePartner f).counter s hs _,by rw [Function.update_self]; exact hs.1⟩

/-- Equal incident prefixes give an actual returning scan bounded linearly in the teams and bits. -/
theorem compareHeaders_run {s : Bank w} (f : BroadcastFrame)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (stable : f.Stable (readings s))
    (good : ∀ i < f.teams, i ≠ f.team → ∀ j < f.header, m (f.addr i j) = m (f.dst+j)) :
    ∃ es t, Runs pub macros compareHeaders s m es t m ∧
      traceCost es ≤ 2+f.teams*(6+f.header*(compareHeaderBit.slots+1)) ∧
      f.Stable (readings t) ∧ (t 11).val = f.teams := by
  obtain ⟨u,init,stable',zero⟩ := partnerStart (pub := pub) (macros := macros) (m := m) f stable
  obtain ⟨es,t,r,c,st,fin⟩ := partnerLoop_complete (stablePartner f) (comparePartner f image fit)
    good u stable' (zero ▸ Nat.zero_le _)
  refine ⟨_,t,init.seq r,?_,st,fin⟩
  change 1 + traceCost es ≤ _
  rw [zero,Nat.sub_zero,show 2+f.header*(compareHeaderBit.slots+1)+4 =
    6+f.header*(compareHeaderBit.slots+1) by omega] at c
  omega

/-- A returning scan validates every word in every incident prefix against the saved copy. -/
theorem compareHeaders_sound {s : Bank w} (f : BroadcastFrame)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (stable : f.Stable (readings s)) {es t mt} (run : Runs pub macros compareHeaders s m es t mt) :
    mt = m ∧ f.Stable (readings t) ∧ (t 11).val = f.teams ∧
      ∀ i < f.teams, i ≠ f.team → ∀ j < f.header, m (f.addr i j) = m (f.dst+j) := by
  obtain ⟨u,init,stable',zero⟩ := partnerStart (pub := pub) (macros := macros) (m := m) f stable
  obtain ⟨u',mu,_,_,_,first,loop⟩ := Runs.seq_iff.mp run
  obtain ⟨_,rfl,rfl⟩ := first.unique_of_deterministic rfl init
  exact partnerLoop_sound (stablePartner f) (comparePartner f image fit) stable' zero loop

end RoutingISA

end BorderVNP
end Computability
end OAI
