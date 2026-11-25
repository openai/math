import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Computability.VPVNP.RAMMemory
import OAI.Hierarchy.DescentTerminalObservationPrefix
import OAI.Hierarchy.DescentTerminalEpochFold
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Fixed physical input addresses for all epoch selector bits -/

namespace Hierarchy.DescentTerminalEpochHeader
open DescentTerminalEpochBits DescentTerminalEpochChart DescentTerminalEpochFlags
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Computability.VPVNP.RAMMemory
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}

structure Shelf (A : Type) where
  source : Source A
  codes : Bank

def directory (lo : ℕ) : List (Source A) → List (Shelf A)
  | [] => []
  | a::ts => ⟨a,⟨lo,Nat.clog 2 a.seats⟩⟩ :: directory (lo+DescentDyadicSpan.span a.seats) ts

def load (w : ℕ) (z : A→Bool) : List (Source A) → ℕ → Word w
  | [],_ => 0
  | a::ts,i => if i < DescentDyadicSpan.span a.seats then header w a.C a.seats (z∘a.pin) i
      else load w z ts (i-DescentDyadicSpan.span a.seats)

def memory (lo : ℕ) (ts : List (Source A)) (z : A→Bool) (previous : Memory w) : Memory w :=
  initialMemory (lo+extent ts) fun a=>if a < lo then previous a else load w z ts (a-lo)

theorem initial_frame (lo : ℕ) (ts : List (Source A)) (z : A→Bool) (previous : Memory w) {i : ℕ} (hi : i < lo) :
    memory lo ts z previous i=previous i := by
  simp [memory,initialMemory,hi,show i < lo+extent ts by omega]

theorem extent_le (ts : List (Source A)) : extent ts ≤ 2*(ts.map Source.seats).sum+ts.length := by
  induction ts with
  | nil=>rfl
  | cons a ts ih=>
    have h:=DescentDyadicSpan.span_le a.seats
    simp only [extent,List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem sources (lo : ℕ) (ts : List (Source A)) : (directory lo ts).map Shelf.source=ts := by
  induction ts generalizing lo with
  | nil=>rfl
  | cons a ts ih=>simp [directory,ih]

theorem placed (lo : ℕ) (ts : List (Source A)) {p : Shelf A} (mem : p∈directory lo ts) :
    lo ≤ p.codes.base ∧ p.source.seats ≤ p.codes.size ∧ p.codes.base + p.codes.size ≤ lo+extent ts := by
  induction ts generalizing lo with
  | nil=>simp [directory] at mem
  | cons a ts ih=>
    rcases List.mem_cons.mp mem with rfl|later
    · exact ⟨le_rfl,Nat.le_pow_clog (by decide) _,by change lo+DescentDyadicSpan.span a.seats ≤ _;unfold extent;omega⟩
    · have h:=ih (lo+DescentDyadicSpan.span a.seats) later
      unfold extent
      exact ⟨by omega,h.2.1,by omega⟩

private theorem read_load (lo : ℕ) (ts : List (Source A)) (z : A→Bool) {p : Shelf A} (mem : p∈directory lo ts)
    (j : Fin p.source.seats) :
    load w z ts (p.codes.base+j.val-lo)=header w p.source.C p.source.seats (z∘p.source.pin) j.val := by
  induction ts generalizing lo with
  | nil=>simp [directory] at mem
  | cons a ts ih=>
    rcases List.mem_cons.mp mem with rfl|later
    · have hi := j.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) a.seats)
      change load w z (a::ts) (lo+j.val-lo)=_
      simp [load,DescentDyadicSpan.span,hi]
    · have room := (placed _ _ later).1
      have outside : ¬p.codes.base+j.val-lo < DescentDyadicSpan.span a.seats := by omega
      rw [load,ite_eq_right outside,show p.codes.base+j.val-lo-DescentDyadicSpan.span a.seats=
        p.codes.base+j.val-(lo+DescentDyadicSpan.span a.seats) by omega]
      exact ih _ later

theorem physical (lo : ℕ) (ts : List (Source A)) (z : A→Bool) (previous : Memory w) {p : Shelf A}
    (member : p∈directory lo ts) (wide : width p.source.C ≤ w) (j : Fin p.source.seats) :
    (memory lo ts z previous (p.codes.base+j.val)).val=raw (z∘p.source.pin) j := by
  have room := placed lo ts member
  have hi := j.isLt.trans_le room.2.1
  have below : p.codes.base+j.val < lo+extent ts := by omega
  have above : ¬p.codes.base+j.val < lo := by omega
  rw [memory,initialMemory,ite_eq_left below,ite_eq_right above,read_load lo ts z member j]
  exact header_word w wide _ j

def native (m : Memory w) (e : EpochRow) : Observation :=
  ⟨e.C,(m e.count).val,e.seats,fun i=>(m (e.codes.base+i.val)).val⟩

/-- A failure may stop the mathematical descent early. All later physical headers can then
contain arbitrary data, since the earlier failure is sticky. A successful decoding uses
the entire fixed source layout. -/
theorem native_survives {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
    (b : Chart bits ok src) (z : b.Pin→Bool) (m : Memory w) (seedAddr : ℕ) (ts : List EpochRow)
    (seed : m seedAddr=0 ↔ ok (z∘b.seed))
    (dates : ts.length=b.layout.length)
    (reached : ∃suffix,ts.map (native m)=b.rows z++suffix) :
    (m seedAddr=0 ∧ ∀e∈ts,(native m e).Valid) ↔ ∃t,b.read z=some t := by
  obtain ⟨suffix,align⟩:=reached
  have values : (∀e∈ts,(native m e).Valid) ↔ ∀o∈ts.map (native m),o.Valid := by simp
  rw [values,align,seed,b.accepted z]
  constructor
  · rintro ⟨s,g⟩
    exact ⟨s,fun o ho=>g o (List.mem_append_left _ ho)⟩
  · rintro ⟨s,g⟩
    obtain ⟨t,h⟩:=(b.accepted z).mpr ⟨s,g⟩
    have n:=congrArg List.length (b.complete z t h)
    have a:=congrArg List.length align
    simp only [List.length_map,List.length_append] at n a
    have empty : suffix=[] := List.eq_nil_of_length_eq_zero (by omega)
    simpa [empty] using And.intro s g

structure Controls where
  rom : Bank
  count : ℕ
  exterior : ℕ
  out : ℕ
  dst : ℕ

def issued (c : Shelf A → Controls) (p : Shelf A) : EpochRow :=
  ⟨p.source.C,(c p).count,p.codes,(c p).rom,p.source.seats,(c p).exterior,(c p).out,(c p).dst⟩

/-- The decoder and the physical checker read the identical fixed raw bit banks.
Only the reached *scalar counts* require matching-stage readbacks. -/
theorem physical_survives {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
    (b : Chart bits ok src) (z : b.Pin→Bool) (lo seedAddr : ℕ) (prev m : Memory w)
    (ctrl : Shelf b.Pin → Controls) (seed : m seedAddr=0 ↔ ok (z∘b.seed))
    (wide : ∀p∈directory lo b.layout,width p.source.C ≤ w)
    (hold : ∀p∈directory lo b.layout,∀i:Fin p.source.seats,
      m (p.codes.base+i.val)=memory lo b.layout z prev (p.codes.base+i.val))
    (counters : List.IsPrefix ((b.rows z).map Observation.count)
      ((directory lo b.layout).map fun p=>(m (ctrl p).count).val)) :
    let ts := (directory lo b.layout).map (issued ctrl)
    (m seedAddr=0 ∧ ∀e∈ts,(native m e).Valid) ↔ ∃t,b.read z=some t := by
  let d := directory lo b.layout
  let ts := d.map (issued ctrl)
  have same : ∀p∈d,(native m (issued ctrl p)).image=p.source.image z := by
    intro p hp
    change (⟨p.source.C,p.source.seats,fun i=>(m (p.codes.base+i.val)).val⟩ : RawImage) = _
    apply congrArg (Sigma.mk p.source.C)
    apply congrArg (Sigma.mk p.source.seats)
    funext i
    rw [hold p hp i]
    exact physical lo b.layout z prev hp (wide p hp) i
  have all : (ts.map (native m)).map Observation.image=b.layout.map (fun p=>p.image z) := by
    rw [←sources lo b.layout]
    simp only [ts,d,List.map_map]
    apply List.map_congr_left
    exact fun p hp=>same p hp
  apply native_survives b z m seedAddr ts seed
  · have l:=congrArg List.length (sources lo b.layout)
    simpa [ts,d] using l
  · obtain ⟨tail,eqn⟩:=b.archived z
    have pre : List.IsPrefix ((b.rows z).map Observation.image) ((ts.map (native m)).map Observation.image) :=
      ⟨tail,(all.trans eqn).symm⟩
    have nums : List.IsPrefix ((b.rows z).map Observation.count) ((ts.map (native m)).map Observation.count) := by
      simpa [ts,d,issued,native,List.map_map,Function.comp_def] using counters
    obtain ⟨rest,h⟩:=prefix_fields pre nums
    exact ⟨rest,h.symm⟩

end
end Hierarchy.DescentTerminalEpochHeader

end OAI
