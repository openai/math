import OAI.Computability.BorderVNP.TeamSiteConsistencyHistory
import OAI.Computability.BorderVNP.TeamSiteConsistencySchedules

/-! # Unique physical team histories of native signed-RAM paths

The charged per-processor executions fix the greedy blocks and all register frames.
The actual input/output rows fix all interior sorter and boundary bits. Together these
checks establish both directions of native path correctness and preserve the signed
path contribution, including a legitimate zero weight.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape RAMTape.PublicExprMachine TeamRAM TeamTapeHandoff TeamContraction.Wires
open TeamTapeSorting TeamTapeInputRoute.Verify
open BurstRAM (Word)
variable {teams w p r k a e : ℕ}

/-- The locally charged events and real shared bits validating a specified finite path.
The trace specifies its entire choice list, including the internal native choices of
each private call. The old-word and record correctness is decided by the physical sorter. -/
def RawHistory.Valid (z : RawHistory teams r w e) (P : TeamOpcode.Program p r k a)
    (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a) (start : TeamOpcode.State w p r)
    (H limit cap : Word w) (input : Fin teams → List Bool) (hw : 2 ≤ w+1)
    (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1)) (es : List (Event w)) (bits : List (List Bool)) : Prop :=
  Scheduled P pub lib start H limit cap es z.blocks z.frames ∧ es.map Event.choices = bits ∧
    z.WireChecks (initial (packed w start.pc.val) start.reg) input hw hc

private theorem valid_block_cost {α : Type*} {f : α → ℕ} {H : ℕ} {bs : List (List α)}
    (h : Team.ValidBlocks f H bs) : ∀ b ∈ bs, RAMBuckets.cost f b ≤ H := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.1
    · exact ih h.2 _ hx

private theorem scheduled_size (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (fits : p ≤ 2^w) (start : TeamOpcode.State w p r)
    (H limit cap : Word w) (input : Fin teams → List Bool) (es : List (Event w))
    (bound : ∀ z ∈ es, z.action.extra ≤ cap.val)
    (own : ∀ j, (input j).length ≤ 3*H.val) (space : 2*H.val ≤ 2^e)
    (blocks : Fin teams → List (Event w)) (out : Fin teams → Frame w r)
    (h : Scheduled P pub lib start H limit cap es blocks out) :
    ∀ j, (realRows input blocks j).length ≤ 4*2^e := by
  obtain ⟨flat,charged,_⟩ := h
  have hb := (charged.spec fits (fun z hz => bound z (flat ▸ hz))).1
  intro j
  have costJ := valid_block_cost hb _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  exact (realRows_length_le input blocks j H.val (own j) costJ).trans (by omega)

/-- Each passing complete physical history yields a true accepting RAM computation.
Soundness is for every individual witness, without a uniqueness assumption. -/
theorem RawHistory.execute_of_valid (z : RawHistory teams r w e) (P : TeamOpcode.Program p r k a)
    (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a) (start : TeamOpcode.State w p r)
    (H limit cap : Word w) (input : Fin teams → List Bool) (hr : 0 < teams) (fits : p ≤ 2^w)
    (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1))
    (header : (List.ofFn input).flatten.length ≤ 2^w) (own : ∀ j, (input j).length ≤ 3*H.val)
    (space : 2*H.val ≤ 2^e) (es : List (Event w)) (bits : List (List Bool))
    (bound : ∀ x ∈ es, x.action.extra ≤ cap.val) (time : cost es ≤ limit.val)
    (ok : z.Valid P pub lib start H limit cap input hw hc es bits) :
    execute (P.fetch pub lib) start (inputMemory w input) bits = some es ∧
      z.links = canonicalLinks hw (internalFrames z.frames) (array e input z.blocks) := by
  obtain ⟨sched,choices,wires⟩ := ok
  have flat := sched.1
  have charged := sched.2.1
  have ne : List.ofFn z.blocks ≠ [] := by simp [List.ofFn_eq_nil_iff,hr.ne']
  have loc := charged.local_initial fits ne
  have clock : 1+cost (List.ofFn z.blocks).flatten ≤ 2^w := by rw [flat]; have := limit.isLt; omega
  have size := scheduled_size P pub lib fits start H limit cap input es bound own space _ _ sched
  have result := (z.wireChecks_iff_execute _ input hr hw hc loc clock header size).mp wires
  rw [flat,choices] at result
  exact ⟨result.2,result.1⟩

/-- A genuine bounded accepting computation extends to one and only one full history:
the actual greedy finite-PC rows, their complete outgoing frames, and every physical
shared sorting and register bit. Every path retains its native choices and sign. -/
theorem execute_iff_unique_rawHistory (P : TeamOpcode.Program p r k a)
    (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a) (start : TeamOpcode.State w p r)
    (H limit cap : Word w) (input : Fin teams → List Bool) (hr : 0 < teams) (fits : p ≤ 2^w)
    (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1))
    (header : (List.ofFn input).flatten.length ≤ 2^w) (own : ∀ j, (input j).length ≤ 3*H.val)
    (space : 2*H.val ≤ 2^e) (es : List (Event w)) (bits : List (List Bool))
    (bound : ∀ x ∈ es, x.action.extra ≤ cap.val) (time : cost es ≤ limit.val)
    (capacity : cost es ≤ teams*(H.val-cap.val)) :
    execute (P.fetch pub lib) start (inputMemory w input) bits = some es ↔
      ∃! z : RawHistory teams r w e, z.Valid P pub lib start H limit cap input hw hc es bits := by
  constructor
  · intro native
    obtain ⟨loc,_,choices⟩ := execute_spec native
    obtain ⟨⟨blocks,out⟩,sched,unique⟩ :=
      TeamSite.existsUnique_schedule P pub lib H limit cap fits hr start es loc bound time capacity
    change Scheduled P pub lib start H limit cap es blocks out at sched
    let z : RawHistory teams r w e := ⟨blocks,out,canonicalLinks hw (internalFrames out) (array e input blocks)⟩
    have flat := sched.1
    have loc' : Local (P.fetch pub lib) start (List.ofFn z.blocks).flatten := flat ▸ loc
    have clock : 1+cost (List.ofFn z.blocks).flatten ≤ 2^w := by rw [show z.blocks = blocks from rfl,flat]; have := limit.isLt; omega
    have size := scheduled_size P pub lib fits start H limit cap input es bound own space _ _ sched
    refine ⟨z,⟨sched,choices,(z.wireChecks_iff_execute _ input hr hw hc loc' clock header size).mpr ⟨rfl,?_⟩⟩,?_⟩
    · simpa only [z,flat,choices] using native
    · rintro ⟨other,frames,links⟩ ok
      have eq := unique (other,frames) ok.1
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      have link := (RawHistory.execute_of_valid _ P pub lib start H limit cap input hr fits hw hc header own space
        es bits bound time ok).2
      exact congrArg (RawHistory.mk other frames) link
  · rintro ⟨z,ok,_⟩
    exact (z.execute_of_valid P pub lib start H limit cap input hr fits hw hc header own space es bits bound time ok).1

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
