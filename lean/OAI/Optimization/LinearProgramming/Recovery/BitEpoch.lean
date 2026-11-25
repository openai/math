import OAI.Optimization.LinearProgramming.Recovery.Restart
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import OAI.Optimization.LinearProgramming.OracleSpec.SubstitutionResources

/-! A finite bit-PCG epoch with an interrupting numerical service. The total Boolean
oracle in this proof returns each actual answer before the first interrupt and then an
arbitrary bit. It supplies the source time certificate used by the physical prefix
simulator, including when an epoch is interrupted before it can return an answer. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace BitEpoch

open OracleSpec
variable {S : Type*}

structure Scan (S : Type*) where
  state : S
  stopped : Bool
  events : List (Event Word)

/-- The transcript is reverse chronological. The fold executes only the genuine
service prefix, retaining its exact post-interrupt state. -/
def scan (serve : S→Word→Reply S) (initial : S) : Transcript → Scan S
  | [] => ⟨initial,false,[]⟩
  | (q,_)::older =>
    let r:=scan serve initial older
    if r.stopped then r else
      match serve r.state q with
      | .answer b t => ⟨t,false,r.events++[(q,some b)]⟩
      | .restart t => ⟨t,true,r.events++[(q,none)]⟩

def reply (serve : S→Word→Reply S) (initial : S) (h : Transcript) (q : Word) : Bool :=
  let r:=scan serve initial h
  if r.stopped then false else
    match serve r.state q with
    | .answer b _ => b
    | .restart _ => false

/-- Encode the chronological successful events in the source machine's history format.
A stopped scan is handled separately and its pending packet has no real answer. -/
def wordHistory (events : List (Event Word)) : Transcript :=
  (events.map fun e=>(e.1,[e.2.getD false])).reverse

inductive Follows (f : Transcript→Word→Bool) : Transcript→Prop where
  | nil : Follows f []
  | answer (q : Word) {h : Transcript} : Follows f h → Follows f ((q,[f h q])::h)

theorem scan_spec (serve : S→Word→Reply S) (initial : S) (h : Transcript) :
    let a:=scan serve initial h
    ServicePath serve initial a.events a.state ∧ restartCount a.events=a.stopped.toNat ∧
    a.events.length ≤ h.length ∧ ∀ e∈a.events,∃ ans,(e.1,ans)∈h := by
  induction h with
  | nil => exact ⟨.nil _,rfl,by simp [scan],by simp [scan]⟩
  | cons pair h ih =>
    obtain ⟨q,raw⟩ := pair
    cases previous : scan serve initial h with
    | mk state stopped events =>
      rw [previous] at ih
      obtain ⟨path,count,len,members⟩ := ih
      cases stopped with
      | true =>
        have update : scan serve initial ((q,raw)::h) = ⟨state,true,events⟩ := by
          simp [scan,previous]
        rw [update]
        refine ⟨path,count,len.trans (Nat.le_succ _),?_⟩
        intro e he
        obtain ⟨ans,old⟩ := members e he
        exact ⟨ans,List.mem_cons_of_mem _ old⟩
      | false =>
        cases act : serve state q with
        | answer b t =>
          have update : scan serve initial ((q,raw)::h) = ⟨t,false,events++[(q,some b)]⟩ := by
            simp [scan,previous,act]
          rw [update]
          refine ⟨path.append (.answer act (.nil _)),?_,?_,?_⟩
          · simpa using count
          · simpa using Nat.succ_le_succ len
          · intro e he
            rcases List.mem_append.mp he with old | last
            · obtain ⟨ans,member⟩ := members e old
              exact ⟨ans,List.mem_cons_of_mem _ member⟩
            · obtain rfl := List.mem_singleton.mp last
              exact ⟨raw,List.mem_cons_self⟩
        | restart t =>
          have update : scan serve initial ((q,raw)::h) = ⟨t,true,events++[(q,none)]⟩ := by
            simp [scan,previous,act]
          rw [update]
          refine ⟨path.append (.restart act (.nil _)),?_,?_,?_⟩
          · have zero : restartCount events=0 := count
            change restartCount (events++[(q,none)])=1
            simp [zero]
          · simpa using Nat.succ_le_succ len
          · intro e he
            rcases List.mem_append.mp he with old | last
            · obtain ⟨ans,member⟩ := members e old
              exact ⟨ans,List.mem_cons_of_mem _ member⟩
            · obtain rfl := List.mem_singleton.mp last
              exact ⟨raw,List.mem_cons_self⟩

theorem clean_history (serve : S→Word→Reply S) (initial : S) {h : Transcript}
    (valid : Follows (reply serve initial) h) (clean : (scan serve initial h).stopped=false) :
    h=wordHistory (scan serve initial h).events := by
  induction valid with
  | nil => rfl
  | @answer q h _ ih =>
    cases previous : scan serve initial h with
    | mk state stopped events =>
      cases stopped with
      | true => simp [scan,previous] at clean
      | false =>
        cases act : serve state q with
        | restart t => simp [scan,previous,act] at clean
        | answer b t =>
          have prior : (scan serve initial h).stopped=false := by simp [previous]
          have old : h=wordHistory events := by simpa only [previous] using ih prior
          have answer : reply serve initial h q=b := by simp [reply,previous,act]
          have update : scan serve initial ((q,[reply serve initial h q])::h) =
              ⟨t,false,events++[(q,some b)]⟩ := by simp [scan,previous,act]
          rw [update,answer]
          change ((q,[b])::h)=wordHistory (events++[(q,some b)])
          simpa [wordHistory] using congrArg ((q,[b])::·) old

theorem run_follows {p : BitProgram} {f : Transcript→Word→Bool} {c t : p.Config} {k : ℕ}
    (run : p.Run (fun h q=>[f h q]) c k t) (start : Follows f c.transcript) :
    Follows f t.transcript ∧ t.transcript.length ≤ c.transcript.length+k := by
  induction run with
  | refl x => exact ⟨start,by omega⟩
  | @step x y z _ cost edge late ih =>
    obtain ⟨pc,_,eq⟩ := BitProgram.tick_decompose edge
    have part : Follows f y.transcript ∧ y.transcript.length ≤ x.transcript.length+cost := by
      cases op : p.instruction pc (x.store (p.scan pc)).head? <;> rw [op] at eq <;> cases eq <;>
        first
        | exact ⟨start,Nat.le_succ _⟩
        | refine ⟨Follows.answer _ start,?_⟩
          change x.transcript.length+1 ≤ x.transcript.length+(1+x.bufferRev.reverse.length+1)
          omega
    obtain ⟨fin,len⟩:=ih part.1
    exact ⟨fin,by omega⟩

/-- Ordinary/cut-oracle bit time is polynomial even for a prefix eventually interrupted.
Geometric consistency in the statement is required only of its actual completed epoch. -/
theorem sealed_epoch {p : BitProgram} {N R budget : ℕ} (anchor : Fin N) (sign : Bool)
    (serve : S→Word→Reply S) (initial : S)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h q=>[f h q]) (priceInput R anchor) budget (pricePost R anchor))
    (consistency : ∀ events t,ServicePath serve initial events t → restartCount events=0 →
      ∃ active : Set (Fin N),∃ costs : Fin N→ℕ,anchor∈active ∧ (∀ j∈active,costs j ≤ R) ∧ priceConsistent sign active costs (wordHistory events)) :
    let f:=reply serve initial
    ∃ k ≤ budget,∃ last : p.Config,p.Run (fun h q=>[f h q]) (p.initial (priceInput R anchor)) k last ∧ last.pc=none ∧
      let actual:=scan serve initial last.transcript
      ServicePath serve initial actual.events actual.state ∧ actual.events.length ≤ k ∧
      (∀ e∈actual.events,∃ i : Fin N,∃ prices : Fin N→ℚ,e.1=priceQuery i prices) ∧
      restartCount actual.events=actual.stopped.toNat ∧ (actual.stopped=false → last.bufferRev.reverse=[sign]) := by
  let f:=reply serve initial
  obtain ⟨k,last,run,time,halt,post⟩:=pcg f
  obtain ⟨follow,length⟩:=run_follows run (.nil)
  change last.transcript.length ≤ 0+k at length
  obtain ⟨path,count,short,members⟩:=scan_spec serve initial last.transcript
  refine ⟨k,time,last,run,halt,path,by omega,?_,count,?_⟩
  · intro e he;obtain ⟨a,ha⟩:=members e he;exact post.1 _ ha
  · intro success
    have zero : restartCount (scan serve initial last.transcript).events=0 := by simpa only [success,Bool.toNat_false] using count
    obtain ⟨active,costs,hi,hR,ok⟩:=consistency _ _ path zero
    exact post.2.2 sign active costs hi hR ((clean_history serve initial follow success).symm ▸ ok)

end BitEpoch
end Recovery
end LinearProgramming
end Optimization
end OAI
