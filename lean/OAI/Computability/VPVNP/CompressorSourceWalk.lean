import OAI.Computability.VPVNP.RAMChain

/-!
# Chronological source kernels in external memory

The native descriptor recipe consists of heterogeneous kernels, with
each segment starting from the data memory produced by the preceding one.
Packets retain the source ordinal, actual input memory and report list
when the online dispatcher inserts its control calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords
open BurstRAM

/-- A sequence of heterogeneous native source kernels operating on one shared
memory. The join keeps their actual reports, including empty phase segments. -/
inductive SourceWalk {w : ℕ} {J : Type*} (source : J → Memory w → List (Report w) → Prop) :
    List J → Memory w → List (Report w) → Prop where
  | done (m) : SourceWalk source [] m []
  | next {j js m rs ts} (head : source j m rs) (tail : SourceWalk source js (after m (eventLog rs)) ts) :
      SourceWalk source (j::js) m (rs++ts)

theorem SourceWalk.after_append {w : ℕ} (m : Memory w) (xs ys : List (Report w)) :
    after m (eventLog (xs++ys)) = after (after m (eventLog xs)) (eventLog ys) := by
  simp only [eventLog,List.flatMap_append,after,List.foldl_append]

theorem SourceWalk.append {w : ℕ} {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    {is js : List J} {m : Memory w} {rs ts : List (Report w)}
    (h : SourceWalk source is m rs) (h' : SourceWalk source js (after m (eventLog rs)) ts) :
    SourceWalk source (is++js) m (rs++ts) := by
  induction h with
  | done => exact h'
  | @next j is m xs ys hx _ ih =>
    rw [after_append] at h'
    simpa only [List.cons_append,List.append_assoc] using SourceWalk.next hx (ih h')

theorem SourceWalk.singleton {w : ℕ} {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    {i : J} {m : Memory w} {rs : List (Report w)} (h : source i m rs) :
    SourceWalk source [i] m rs := by simpa using SourceWalk.next h (SourceWalk.done _)

namespace SourceWalk

/-- A source stage together with its entry memory and sequence of native reports. -/
structure Packet (J : Type*) (w : ℕ) where
  /-- Source stage executed to produce this packet. -/
  stage : J
  /-- Memory supplied to the source stage before its first call. -/
  input : Memory w
  /-- Reports returned by the stage in execution order. -/
  reports : List (Report w)

/-- Memory obtained by replaying the packet's reports on its entry memory. -/
def Packet.output {w : ℕ} {J : Type*} (p : Packet J w) := after p.input (eventLog p.reports)

/-- Each packet runs its named stage on the preceding packet's output, beginning with the
supplied memory. -/
def Chronological {w : ℕ} {J : Type*} (source : J → Memory w → List (Report w) → Prop) :
    Memory w → List (Packet J w) → Prop
  | _, [] => True
  | m, p::ps => p.input = m ∧ source p.stage p.input p.reports ∧ Chronological source p.output ps

theorem packets {w : ℕ} {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    {js : List J} {m : Memory w} {rs : List (Report w)} (h : SourceWalk source js m rs) :
    ∃ ps : List (Packet J w), ps.map Packet.stage = js ∧ ps.flatMap Packet.reports = rs ∧ Chronological source m ps := by
  induction h with
  | done => exact ⟨[],rfl,rfl,trivial⟩
  | @next j js m xs ys hx _ ih =>
    obtain ⟨ps,hjs,hrs,hchron⟩ := ih
    refine ⟨⟨j,m,xs⟩::ps,?_,?_,rfl,hx,hchron⟩
    · simp only [List.map_cons,hjs]
    · simp only [List.flatMap_cons,hrs]

theorem report_count {w : ℕ} {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    {js : List J} {m : Memory w} {rs : List (Report w)} (h : SourceWalk source js m rs) (count : J → ℕ)
    (hc : ∀ j m rs, source j m rs → rs.length = count j) : rs.length = (js.map count).sum := by
  induction h with
  | done => rfl
  | next h _ ih => rw [List.length_append,List.map_cons,List.sum_cons,hc _ _ _ h,ih]

end SourceWalk
end CompressorRecords

end VPVNP
end Computability
end OAI
