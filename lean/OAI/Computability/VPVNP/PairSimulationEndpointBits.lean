import OAI.Computability.VPVNP.PairSimulationFinalBits

/-!
# Reading a final arc inside a vertex call

The five-opcode loop reads a contiguous final arc from external memory and
copies its bits into the private tape of the current vertex. It can be entered
at each source or target incidence with new interval bounds. Its continuation
keeps all private cells outside that interval, and the external memory and
branch stream are available to the rest of the vertex expansion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.EndpointBits

open BurstRAM BurstRAM.PrivateRAM FinalBits PrimedInputRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {a : ℕ} (h : a < 2 ^ w) : (word w a).val = a :=
  Nat.mod_eq_of_lt h

/-- Registers hold the current source, exclusive source end, current private
destination, one, and a temporary word. -/
def instruction (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) : Fin 5 → Instr w p r k :=
  ![.jumpEq (reg 0) (reg 1) done (pc 1), .readExternal (reg 4) (reg 0) (pc 2),
    .storePrivate (reg 2) (reg 4) (pc 3), .binary .add (reg 2) (reg 2) (reg 3) (pc 4),
    .binary .add (reg 0) (reg 0) (reg 3) (pc 0)]

/-- The vertex reader has the same opcodes and jump targets at every word width. -/
theorem resize_instruction (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) (i : Fin 5) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- Require the five endpoint-copy instructions at the supplied program counters. Each
iteration loads one external arc cell into the private tape and advances both cursors until
control reaches `done`. -/
def Linked (M : Machine w p r k) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

variable {M : Machine w p r k} {pc : Fin 5 → Fin p} {reg : Fin 5 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 5) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- Actual chronological events, including the loop exit test at width zero. -/
def events (m : Memory w) (src : ℕ) : ℕ → List (Event w)
  | 0 => [.tick]
  | n+1 => [.tick, .read (word w src) (m src), .tick, .tick, .tick] ++ events m (src+1) n

theorem probes (m : Memory w) (src n : ℕ) : countProbes (events m src n) = n := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih => simp [events, countProbes, ih, Nat.add_comm]

/-- Closed form for the private-memory slice after the loop. -/
def copySlice (m : Memory w) (src dst n : ℕ) (old : Word w → Word w) (a : Word w) : Word w :=
  if dst ≤ a.val ∧ a.val < dst+n then m (src + (a.val-dst)) else old a

private theorem copySlice_succ (m : Memory w) (src dst n : ℕ) (old : Word w → Word w)
    (hd : dst < 2 ^ w) :
    copySlice m (src+1) (dst+1) n (Function.update old (word w dst) (m src)) =
      copySlice m src dst (n+1) old := by
  funext a
  by_cases ha : a.val = dst
  · have he : a = word w dst := Fin.ext (ha.trans (val_word hd).symm)
    simp [copySlice, he, val_word hd]
  · have he : a ≠ word w dst := fun e ↦ ha ((congrArg Fin.val e).trans (val_word hd))
    simp only [copySlice, Function.update_of_ne he]
    split_ifs with h h' h' <;> first | rfl | (congr 1; omega)

private def advance (c : Config w p r) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r)
    (src dst : ℕ) (value : Word w) : Config w p r :=
  let cr := {c with pc := pc 1}
  let ct := cr.put (pc 2) (reg 4) value
  let cs := ct.store (pc 3) (word w dst) value
  let cd := cs.put (pc 4) (reg 2) (word w (dst+1))
  cd.put (pc 0) (reg 0) (word w (src+1))

private theorem local_step {c d : Config w p r} (hs : M.program.step c = .localStep d)
    (fuel : ℕ) (m : Memory w) (bs : List Bool) :
    execute M.program (fuel+1) c m bs = (execute M.program fuel d m bs).map
      (Report.prepend .tick) := by
  simp only [execute, hs]

private theorem read_step {c : Config w p r} {a : Word w} {g : Word w → Config w p r}
    (hs : M.program.step c = .read a g) (fuel : ℕ) (m : Memory w) (bs : List Bool) :
    execute M.program (fuel+1) c m bs = (execute M.program fuel (g (m a.val)) m bs).map
      (Report.prepend (.read a (m a.val))) := by
  simp only [execute, hs]

private theorem execute_body (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (m : Memory w) (src dst : ℕ) (hs : src < 2 ^ w) (hr : c.reg (reg 0) = word w src)
    (hd : c.reg (reg 2) = word w dst) (h1 : c.reg (reg 3) = 1) (hn : c.reg (reg 0) ≠ c.reg (reg 1))
    (fuel : ℕ) (bs : List Bool) :
    execute M.program (fuel+5) c m bs =
      (execute M.program fuel (advance c pc reg src dst (m src)) m bs).map
        (fun rep ↦ ⟨[.tick, .read (word w src) (m src), .tick, .tick, .tick] ++ rep.events,
          rep.result⟩) := by
  let cr := {c with pc := pc 1}
  let ct := cr.put (pc 2) (reg 4) (m src)
  let cs := ct.store (pc 3) (word w dst) (m src)
  let cd := cs.put (pc 4) (reg 2) (word w (dst+1))
  have s0 : M.program.step c = .localStep cr := by
    rw [step_at hl 0 c hc]
    change CallAction.localStep {c with
      pc := if c.reg (reg 0) = c.reg (reg 1) then done else pc 1} = _
    simp [hn, cr]
  have s1 : M.program.step cr = .read (word w src) (fun v ↦ cr.put (pc 2) (reg 4) v) := by
    rw [step_at hl 1 cr rfl]
    change CallAction.read (c.reg (reg 0)) _ = _
    rw [hr]
  have s2 : M.program.step ct = .localStep cs := by
    rw [step_at hl 2 ct rfl]
    change CallAction.localStep (ct.store (pc 3) (ct.reg (reg 2)) (ct.reg (reg 4))) = _
    simp [cs, ct, cr, Config.put, hd]
  have s3 : M.program.step cs = .localStep cd := by
    rw [step_at hl 3 cs rfl]
    change CallAction.localStep (cs.put (pc 4) (reg 2) (cs.reg (reg 2) + cs.reg (reg 3))) = _
    simp [cd, cs, ct, cr, Config.store, Config.put, hd, h1, word]
  have s4 : M.program.step cd = .localStep (advance c pc reg src dst (m src)) := by
    rw [step_at hl 4 cd rfl]
    change CallAction.localStep (cd.put (pc 0) (reg 0) (cd.reg (reg 0) + cd.reg (reg 3))) = _
    simp [advance, cd, cs, ct, cr, Config.store, Config.put, hr, h1, word]
  have hread : execute M.program (fuel+4) cr m bs =
      (execute M.program (fuel+3) ct m bs).map (Report.prepend (.read (word w src) (m src))) := by
    rw [read_step s1, val_word hs]
  rw [local_step s0, hread, local_step s2, local_step s3, local_step s4]
  simp [Option.map_map, Function.comp_def, Report.prepend]

/-- Exact native execution inside an arbitrary vertex call. There is one
read per incident bit and no private branches. The updated private slice is
available to an arbitrary continuation at the chosen exit. -/
theorem execute_arc (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (m : Memory w) (src dst n : ℕ) (hsrc : src + n < 2 ^ w) (hdst : dst + n < 2 ^ w)
    (hread : c.reg (reg 0) = word w src) (hend : c.reg (reg 1) = word w (src + n))
    (hwrite : c.reg (reg 2) = word w dst) (hone : c.reg (reg 3) = 1) :
    ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧
      out.reg (reg 0) = word w (src+n) ∧ out.reg (reg 2) = word w (dst+n) ∧
      (∀ i, i ≠ reg 0 → i ≠ reg 2 → i ≠ reg 4 → out.reg i = c.reg i) ∧
      out.privateMem = copySlice m src dst n c.privateMem ∧
      ∀ fuel bs, execute M.program (fuel + 5*n+1) c m bs =
        (execute M.program fuel out m bs).map (fun rep ↦ ⟨events m src n ++ rep.events,
          rep.result⟩) := by
  induction n generalizing c src dst with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := hread.trans (by simpa using hend.symm)
    have s0 : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 0 c hc]
      change CallAction.localStep {c with
        pc := if c.reg (reg 0) = c.reg (reg 1) then done else pc 1} = _
      simp [he]
    refine ⟨{c with pc := done}, rfl, rfl, by simpa using hread, by simpa using hwrite,
      fun _ _ _ _ ↦ rfl, ?_, ?_⟩
    · funext a
      simp [copySlice]
    · intro fuel bs
      simp [execute, s0, events]
      rfl
  | succ n ih =>
    let next := advance c pc reg src dst (m src)
    have ne : c.reg (reg 0) ≠ c.reg (reg 1) := by
      rw [hread, hend]
      intro e
      have hv := congrArg Fin.val e
      rw [val_word (by omega : src < 2^w), val_word hsrc] at hv
      omega
    have es : src+1+n = src+(n+1) := by omega
    have ed : dst+1+n = dst+(n+1) := by omega
    have regOther (i : Fin r) (h0 : i ≠ reg 0) (h2 : i ≠ reg 2) (h4 : i ≠ reg 4) :
        next.reg i = c.reg i := by
      simp [next, advance, Config.put, Config.store, Function.update_of_ne, h0, h2, h4]
    obtain ⟨out, ho, hp, ha, hb, hrest, hpriv, hex⟩ := ih next rfl (src+1) (dst+1)
      (es ▸ hsrc) (ed ▸ hdst) (by simp [next, advance, Config.put])
      (by rw [regOther, es, hend] <;> simp)
      (by simp [next, advance, Config.put]) (by rw [regOther, hone] <;> simp)
    refine ⟨out, ho, hp, es ▸ ha, ed ▸ hb, fun i h0 h2 h4 ↦ (hrest i h0 h2 h4).trans
      (regOther i h0 h2 h4), hpriv.trans (copySlice_succ _ _ _ _ _ (by omega)), ?_⟩
    intro fuel bs
    rw [show fuel + 5*(n+1)+1 = (fuel+5*n+1)+5 by omega,
      execute_body hl c hc m src dst (by omega) hread hwrite hone ne]
    change (execute M.program _ next m bs).map _ = _
    rw [hex]
    simp [Option.map_map, Function.comp_def, events]

variable {E : ℕ} (width : Fin E → ℕ)

/-- Beginning of an arc relative to the lower address of the bit array. -/
def offset (e : Fin E) : ℕ := ∑ i : Fin e, width (Fin.castLE e.isLt.le i)

theorem arc_fits (e : Fin E) : offset width e + width e ≤ ∑ t, width t := by
  have h := Finset.sum_le_univ_sum_of_nonneg (s := Finset.univ.map (Fin.castLEEmb e.isLt))
    (fun t ↦ Nat.zero_le (width t))
  rw [Finset.sum_map, Fin.sum_univ_castSucc] at h
  exact h

variable (N : NetworkKernel.Network) (number : N.Edge ≃ Fin E)
  (encode : ∀ e, N.Payload e ≃ (Fin (width (number e)) → Bool))

/-- An incidence reader linked inside a final vertex call copies exactly the
edge payload of equation (7.1) into its private workspace. The copy executes
from the first loop opcode, including for a zero-width edge. -/
theorem execute_payload (hl : Linked M pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (low : ℕ) (fit : low + ∑ t, width t < 2 ^ w) (f : Fin (∑ t,
      width t) → Bool) (initial : Memory w)
    (e : N.Edge) (dst : ℕ) (hdst : dst + width (number e) < 2 ^ w)
    (hread : c.reg (reg 0) = word w (low + offset width (number e)))
    (hend : c.reg (reg 1) = word w (low + offset width (number e) + width (number e)))
    (hwrite : c.reg (reg 2) = word w dst) (hone : c.reg (reg 3) = 1) :
    let mem := after initial (eventLog (reports w low f))
    let src := low + offset width (number e)
    let n := width (number e)
    ∃ out, out.pc = done ∧
      (∀ j : Fin n, out.privateMem (word w (dst+j)) =
        encodeBit w (encode e (payloads width N number encode f e) j)) ∧
      ∀ fuel bs, execute M.program (fuel + 5*n+1) c mem bs =
        (execute M.program fuel out mem bs).map (fun rep ↦ ⟨events mem src n ++ rep.events,
          rep.result⟩) := by
  dsimp only
  have bound := arc_fits width (number e)
  obtain ⟨out,ho,_,_,_,_,hm,run⟩ := execute_arc hl c hc _ _ _ _
    (by omega) hdst hread hend hwrite hone
  refine ⟨out, ho, ?_, run⟩
  intro j
  have hj := j.isLt
  have ha : (word w (dst+j)).val = dst+j := val_word (by omega)
  rw [hm, payloads_bit, copySlice, ha]
  have hi : dst ≤ dst+j ∧ dst+j < dst+width (number e) := ⟨by omega, by omega⟩
  simp only [hi, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  have hj' := index_val width (number e) j
  change (index width (number e) j).val = offset width (number e) + j.val at hj'
  rw [Nat.add_assoc, ← hj', readback low fit]

/-- Summing the native reader's probe counts at the source and target of
every arc gives twice the total bit width. Loops contribute both incidences. -/
theorem endpoint_probe_total [DecidableEq N.Site] (m : Memory w) (low : ℕ) :
    (∑ v : N.Site, ∑ e : N.Edge,
      ((if v = N.src e then countProbes (events m (low + offset width (number e)) (width
        (number e))) else 0) +
      (if v = N.dst e then countProbes (events m (low + offset width (number e)) (width
        (number e))) else 0))) =
      2 * ∑ t, width t := by
  rw [Finset.sum_comm]
  simp [probes, Finset.sum_add_distrib, number.sum_comp, two_mul]

end PairSimulation.EndpointBits

end VPVNP
end Computability
end OAI
