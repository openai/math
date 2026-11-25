import OAI.Computability.MultitapeWeakETH.PackedSwitches

/-! # Encoding independent stage registers in the actual lifted wire payloads -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open NearSquareRoot.Benes VPVNP VPVNP.Compression VPVNP.NetworkKernel
open scoped Classical
noncomputable section

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)

abbrev Registers (m g l : ℕ) := Fin (m+2) → Word (g+l) → Bool
abbrev Payloads (stages : Fin (m+2) → Bool × ℕ) (a g l : ℕ) :=
  (e : (state stages a g l).network.Edge) → (state stages a g l).network.Payload e

def switchAt (i : Fin (m+2)) : Equiv.Perm (Word (g+l)) :=
  stagePerm t (stages i).1 (stages i).2

def portAt (i : Fin (m+2)) (x : Word (g+l)) :=
  selected ha (flips t (stages i).1 (stages i).2 x)

theorem portAt_lt (i : Fin (m+2)) (x : Word (g+l)) :
    (portAt stages t ha i x).val < 2 := by
  unfold portAt selected
  split <;> simp

def edgeAt (i : Fin (m+2)) (x : Word (g+l)) : (state stages a g l).network.Edge :=
  ((i,lane x),portAt stages t ha i x)

theorem edgeAt_dst (i : Fin (m+2)) (x : Word (g+l)) :
    (state stages a g l).network.dst (edgeAt stages t ha i x) =
      (finRotate _ i,lane (switchAt stages t i x)) := target ha t i x

def offsetAt (i : Fin (m+2)) (x : Word (g+l)) :
    Fin ((state stages a g l).width ((i,portAt stages t ha i x),lane x)) :=
  ⟨(packed g l x).2.val, by
    change _ < if _ then _ else _
    rw [ite_eq_left (portAt_lt stages t ha i x)]
    exact (packed g l x).2.isLt⟩

def read (z : Payloads stages a g l) : Registers m g l :=
  fun i x => z (edgeAt stages t ha i x) (offsetAt stages t ha i x)

/-- Fill the selected slot at each address. Bits on the unused slot are zero,
and padding slots have no bit indices at all. -/
def write (r : Registers m g l) : Payloads stages a g l :=
  fun e k =>
    let i := e.1.1
    let slot := e.2
    if h : slot.val < 2 then
      let off : Fin (2^l) := ⟨k.val,by
        have hk := k.isLt
        change _ < (if slot.val < 2 then 2^l else 0) at hk
        simpa [h] using hk⟩
      let x := (packed g l).symm (e.1.2,off)
      if portAt stages t ha i x = slot then r i x else false
    else false

theorem read_write (r : Registers m g l) : read stages t ha (write stages t ha r) = r := by
  funext i x
  simp only [read,write,edgeAt,portAt_lt,dite_true,offsetAt,lane,Fin.eta,Prod.mk.eta,
    Equiv.symm_apply_apply,ite_true]

/-- Physical clamp on a site's outgoing half-wires. -/
def Clamped (v : (state stages a g l).network.Site) (z : (state stages a g l).network.Half v) : Prop :=
  ∀ (x : Word (g+l)) (hx : lane x = v.2) (s : Fin (2^a)) (hs : s.val < 2),
    s ≠ portAt stages t ha v.1 x →
      z.1 (v,s) rfl ⟨(packed g l x).2.val,by
        change _ < (if _ then _ else _)
        rw [ite_eq_left hs]
        exact (packed g l x).2.isLt⟩ = false

theorem write_clamped (r : Registers m g l) (v : (state stages a g l).network.Site) :
    Clamped stages t ha v (WireTensor.edgeAssignment _ _ (write stages t ha r) v) := by
  intro x hx s hs ne
  have eq : (packed g l).symm (v.2,(packed g l x).2) = x := by
    rw [← hx]; exact (packed g l).symm_apply_apply x
  change write stages t ha r (v,s) _ = false
  simp only [write,hs,dite_true,Fin.eta,eq,ite_eq_right (Ne.symm ne)]

theorem write_read (z : Payloads stages a g l)
    (clamp : ∀ v, Clamped stages t ha v (WireTensor.edgeAssignment _ _ z v)) :
    write stages t ha (read stages t ha z) = z := by
  funext e k
  obtain ⟨⟨i,v⟩,s⟩ := e
  by_cases hs : s.val < 2
  · let off : Fin (2^l) := ⟨k.val,by
      have hk := k.isLt
      change _ < (if s.val < 2 then 2^l else 0) at hk
      simpa [hs] using hk⟩
    let x := (packed g l).symm (v,off)
    have eq : packed g l x = (v,off) := (packed g l).apply_symm_apply _
    have hv : lane x = v := congrArg Prod.fst eq
    have ho : (packed g l x).2 = off := congrArg Prod.snd eq
    by_cases matchPort : portAt stages t ha i x = s
    · simp only [write,hs,dite_true]
      change (if portAt stages t ha i x = s then read stages t ha z i x else false) = _
      rw [ite_eq_left matchPort]
      unfold read edgeAt
      congr 1
      · exact Prod.ext (Prod.ext rfl hv) matchPort
      · apply (Fin.heq_ext_iff (by change (if (portAt stages t ha i x).val < 2 then 2^l else 0) =
            (if s.val < 2 then 2^l else 0); rw [matchPort])).mpr
        exact congrArg Fin.val ho
    · have hc := clamp (i,v) x hv s hs (Ne.symm matchPort)
      simp only [write,hs,dite_true]
      change (if portAt stages t ha i x = s then read stages t ha z i x else false) = _
      rw [ite_eq_right matchPort]
      exact (by simpa [WireTensor.edgeAssignment,ho,off] using hc.symm)
  · have hk := k.isLt
    change _ < (if s.val < 2 then 2^l else 0) at hk
    simp [hs] at hk

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
