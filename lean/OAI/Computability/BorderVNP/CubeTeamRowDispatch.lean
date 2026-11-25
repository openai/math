import OAI.Computability.BorderVNP.CubeTeamRowPrepare
import OAI.Computability.BorderVNP.CubeISAOwnedTrace

/-! # Dispatch of the two physical row programs on one team

Each ordered pair (s,t) addresses the endpoint view at group s. The first guard
reads the actual group-owner table. The second chooses the repeated-symbol or
strict-pair program. Both owned sides of a co-located strict pair are visited,
with their own directed input views and their respective local vertices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Enter only this team's endpoint, with the diagonal case selected by its two symbols. -/
def select (strict diagonal : Code) : Code :=
  .ifEq 46 47 (.ifEq 48 49 diagonal strict) .nop

/-- Advance the reserved row ordinal without depending on any callback scratch value. -/
def advance : Code := .seq (.constant 59 1) (.binary .add 22 22 59)

/-- Physical row preparation, owner selection and the cursor advance. -/
def body (strict diagonal : Code) : Code :=
  TeamRowPrepare.prepare.seq ((select strict diagonal).seq advance)

/-- Complete ordered-symbol scan at one team. -/
def scan (strict diagonal : Code) : Code :=
  TeamRowPrepare.setup.seq (.whileLt 22 23 (body strict diagonal))

/-- Chronological private bits from this team's roles alone. -/
def choices (l : TeamRowPrepare.Layout) (owner : ℕ → ℕ) (bits : ℕ → List Bool) :=
  (List.range (l.d*l.d)).flatMap fun q => if owner (q/l.d) = l.teamID then bits q else []

/-- Constant classification work at every ordered pair, with local work charged only
to the group that the physical owner table assigns to this team. -/
def ticks (l : TeamRowPrepare.Layout) (owner cost : ℕ → ℕ) :=
  TeamRowPrepare.setup.slots + (∑ q ∈ Finset.range (l.d*l.d),
    (TeamRowPrepare.prepare.slots+5 + if owner (q/l.d) = l.teamID then cost q else 0)) + 1

/-- An unsigned setup or preparation also preserves the vertex-directory cursor
whenever the assembled code never assigns register 7. -/
private theorem prepare_trace {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s : Bank w} {m : Memory w} {n : ℕ} {P : NatState → Prop}
    (run : BoundedRun pub mac c s m n P) (unsigned : c.unsigned = true) (h7 : c.keeps 7 = true) :
    TraceRun pub mac c s m [] n (fun t mt => P (.ofWords t mt) ∧ t 7 = s 7) := by
  obtain ⟨es,t,mt,r,tr,cap,h⟩ := traceRun_unsigned run unsigned
  exact ⟨_,_,_,r,tr,cap,h,r.keepsReg h7⟩

private theorem run_advance {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (i N : ℕ) (hi : i < N) (hc : readings s 22 = i)
    (hN : readings s 23 = N) :
    TraceRun pub mac advance s m [] 2 (fun t mt =>
      readings t 22 = i+1 ∧ readings t 23 = N ∧ t 7 = s 7 ∧ mt = m) := by
  have fit : i+1 < 2^w := Nat.lt_of_le_of_lt hi (hN ▸ (show readings s 23 < _ from (s 23).isLt))
  have one : 1 < 2^w := by omega
  have saf : advance.fixedSafe w (readings pub) (.ofWords s m) := by
    simp [advance,Code.fixedSafe,Code.fixedEval,Code.evalNat,Code.safeReadOnly,addressOpFits,NatState.ofWords,hc]
    exact ⟨fun he => by subst w; simp at one,fit⟩
  obtain ⟨es,t,mt,r,tr,cap,eqn,h7⟩ := prepare_trace (advance.runFixed pub mac s m saf) (by decide) (by decide)
  have rg := congrArg NatState.reg eqn
  refine ⟨_,_,_,r,tr,cap,?_,?_,h7,?_⟩
  · have e := congrFun rg 22
    simpa (config := {decide := true}) [advance,Code.fixedEval,Code.evalNat,NatState.ofWords,addressOp,hc] using e
  · exact (congrArg Fin.val (r.keepsReg (k := 23) (by decide))).trans hN
  · funext a
    exact Fin.ext (congrFun (congrArg NatState.mem eqn) a)

/-- A returning role body has advanced the semantic row prefix and retained the
two outer loop registers. The vertex cursor and all memory words are part of
the semantic prefix state. -/
def Next {w : ℕ} (l : TeamRowPrepare.Layout) (I : ℕ → Word w → Memory w → Prop)
    (q : ℕ) (t : Bank w) (mt : Memory w) :=
  I (q+1) (t 7) mt ∧ readings t 22 = q ∧ readings t 23 = l.d*l.d

private theorem select_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (strict diagonal : Code) (l : TeamRowPrepare.Layout) (owner cost : ℕ → ℕ) (bits : ℕ → List Bool)
    (I : ℕ → Word w → Memory w → Prop) (q : ℕ) (s : Bank w) (m : Memory w)
    (ready : TeamRowPrepare.ReadyRow l (readings m) q (.ofWords s m))
    (own : readings m (l.ownerBase+q/l.d) = owner (q/l.d))
    (skip : owner (q/l.d) ≠ l.teamID → I (q+1) (s 7) m)
    (diag : owner (q/l.d) = l.teamID → q/l.d = q%l.d →
      TraceRun pub mac diagonal s m (bits q) (cost q) (Next l I q))
    (both : owner (q/l.d) = l.teamID → q/l.d ≠ q%l.d →
      TraceRun pub mac strict s m (bits q) (cost q) (Next l I q)) :
    TraceRun pub mac (select strict diagonal) s m
      (if owner (q/l.d) = l.teamID then bits q else [])
      (2 + if owner (q/l.d) = l.teamID then cost q else 0) (Next l I q) := by
  have hteam : s 46 = s 47 ↔ owner (q/l.d) = l.teamID := by
    rw [← Fin.val_inj,show (s 46).val = _ from ready.owner,own,show (s 47).val = _ from ready.team]
  have hpair : s 48 = s 49 ↔ q/l.d = q%l.d := by
    rw [← Fin.val_inj,show (s 48).val = _ from ready.left,show (s 49).val = _ from ready.right]
  by_cases ho : owner (q/l.d) = l.teamID
  · rw [ite_eq_left ho,ite_eq_left ho]
    have chosen : TraceRun pub mac (if s 48 = s 49 then diagonal else strict)
        s m (bits q) (cost q) (Next l I q) := by
      by_cases he : q/l.d = q%l.d
      · rw [ite_eq_left (hpair.mpr he)]
        exact diag ho he
      · rw [ite_eq_right (hpair.not.mpr he)]
        exact both ho he
    have inner := TraceRun.branch chosen
    have outer : TraceRun pub mac (if s 46 = s 47 then Code.ifEq 48 49 diagonal strict else .nop)
        s m (bits q) (1+cost q) (Next l I q) := by simpa [hteam.mpr ho] using inner
    exact outer.branch.mono (by omega) (fun _ _ h => h)
  · rw [ite_eq_right ho,ite_eq_right ho]
    have r : Runs pub mac .nop s m [RoutingISA.tick w] s m := Runs.localStep m rfl rfl
    have outer : TraceRun pub mac (if s 46 = s 47 then Code.ifEq 48 49 diagonal strict else .nop)
        s m [] 1 (Next l I q) := by
      rw [ite_eq_right (hteam.not.mpr ho)]
      exact ⟨_,_,_,r,by simp [DiagonalResidueRAM.TraceOK,RoutingISA.tick],le_rfl,
        skip ho,ready.cursor,ready.bound⟩
    exact outer.branch

/-- The full ordered physical scan concatenates the private bits of exactly the
team's owned row roles. Its final memory and vertex cursor satisfy the last
prefix of the supplied row invariant. -/
theorem scan_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (strict diagonal : Code) (l : TeamRowPrepare.Layout) (owner cost : ℕ → ℕ) (bits : ℕ → List Bool)
    (I : ℕ → Word w → Memory w → Prop) (s : Bank w) (m : Memory w)
    (fit : l.Fits w) (hf : readings pub 0 = l.frame) (start : I 0 (s 7) m)
    (inventory : ∀ q u mu, I q u mu → l.Fields (readings mu) ∧
      ∀ g < l.d, readings mu (l.ownerBase+g) = owner g)
    (skip : ∀ q < l.d*l.d, owner (q/l.d) ≠ l.teamID → ∀ u mu, I q u mu → I (q+1) u mu)
    (visit : ∀ q < l.d*l.d, owner (q/l.d) = l.teamID → ∀ u mu, I q (u 7) mu →
      TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu) →
      TraceRun pub mac (if q/l.d = q%l.d then diagonal else strict) u mu (bits q) (cost q) (Next l I q)) :
    TraceRun pub mac (scan strict diagonal) s m (choices l owner bits) (ticks l owner cost)
      (fun t mt => I (l.d*l.d) (t 7) mt ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d) := by
  let N := l.d*l.d
  let B q := if owner (q/l.d) = l.teamID then bits q else []
  let C q := if owner (q/l.d) = l.teamID then cost q else 0
  let J (q : ℕ) (t : Bank w) (mt : Memory w) :=
    I q (t 7) mt ∧ readings t 22 = q ∧ readings t 23 = N
  have regs (q : ℕ) (t : Bank w) (mt : Memory w) (h : J q t mt) :
      readings t 22 = q ∧ readings t 23 = N := h.2
  have step (q : ℕ) (hq : q < N) (t : Bank w) (mt : Memory w) (h : J q t mt) :
      TraceRun pub mac (body strict diagonal) t mt (B q)
        (TeamRowPrepare.prepare.slots + (2+C q+2)) (J (q+1)) := by
    obtain ⟨fields,owners⟩ := inventory q (t 7) mt h.1
    have hd : 0 < l.d := by
      change q < l.d*l.d at hq
      by_contra! he
      rw [Nat.eq_zero_of_le_zero he] at hq
      omega
    have gfit : q/l.d < l.d := (Nat.div_lt_iff_lt_mul hd).2 hq
    have prep := prepare_trace
      (TeamRowPrepare.run_prepare pub mac l t mt q fit hf fields hq h.2.1 h.2.2)
      (by decide) TeamRowPrepare.prepare_keeps
    have next (u : Bank w) (mu : Memory w) (rd : TeamRowPrepare.ReadyRow l (readings mt) q (.ofWords u mu))
        (r7 : u 7 = t 7) :
        TraceRun pub mac ((select strict diagonal).seq advance) u mu ((B q)++[])
          (2+C q+2) (J (q+1)) := by
      obtain rfl : mu = mt := funext fun a => Fin.ext (congrFun rd.mem a)
      have inv : I q (u 7) mu := r7 ▸ h.1
      have sel := select_run pub mac strict diagonal l owner cost bits I q u mu rd
        (owners _ gfit) (fun ho => skip q hq ho (u 7) mu inv)
        (fun ho he => by simpa [he] using visit q hq ho u mu inv rd)
        (fun ho he => by simpa [he] using visit q hq ho u mu inv rd)
      apply sel.seq
      intro v mv hv
      apply (run_advance pub mac v mv q N hq hv.2.1 hv.2.2).mono le_rfl
      rintro a ma ⟨ha,hb,h7,rfl⟩
      exact ⟨h7 ▸ hv.1,ha,hb⟩
    have run := prep.seq (fun u mu hpre => next u mu hpre.1 hpre.2)
    simpa only [body,List.nil_append,List.append_nil] using run
  have init := prepare_trace (TeamRowPrepare.run_setup pub mac l s m fit hf (inventory _ _ _ start).1)
    (by decide) TeamRowPrepare.setup_keeps
  have tail (u : Bank w) (mu : Memory w) (h22 : readings u 22 = 0) (h23 : readings u 23 = N)
      (hm : readings mu = readings m) (h7 : u 7 = s 7) :=
    trace_counted 22 23 (body strict diagonal) N (fun q => TeamRowPrepare.prepare.slots+(2+C q+2))
      B J regs step 0 (Nat.zero_le _) u mu (show J 0 u mu by
        have he : mu = m := funext fun a => Fin.ext (congrFun hm a)
        exact ⟨he ▸ h7 ▸ start,h22,h23⟩)
  have run := init.seq (fun u mu h => tail u mu h.1.1 h.1.2.1 h.1.2.2 h.2)
  have tickEq : ∀ q, TeamRowPrepare.prepare.slots+(2+C q+2)+1 =
      TeamRowPrepare.prepare.slots+5+C q := by intro q; omega
  simp only [tickEq] at run
  simpa only [choices,ticks,scan,N,J,List.nil_append,Nat.sub_zero,← List.range_eq_range',
    Nat.Ico_zero_eq_range,C,B,Nat.add_assoc] using run

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
