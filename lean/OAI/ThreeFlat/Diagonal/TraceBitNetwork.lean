import OAI.ThreeFlat.Diagonal.LaneCursorCanonical
import OAI.ThreeFlat.Diagonal.TraceRestrictPins
import OAI.ThreeFlat.Diagonal.TraceStaticLayout
import OAI.ThreeFlat.Diagonal.TraceStaticDescriptor

namespace OAI
/-! # The uniform computation on exactly its open bit inputs -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM RAMSerialization RAMMemory LaneCursor
variable {F : Type*} {n P Q S w k low slots offset : ℕ}

variable [Fintype F] [CommRing F] {p r k' d f : ℕ}

noncomputable def network (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' d : ℕ) : BitNetwork F S :=
  (TraceStaticRow.network hF hw hp base st hs hf r k' d).restrictPins bitPin

@[simp] theorem count_cells (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' d : ℕ) :
    (network hF hw hp base st hs hf r k' d).cells = 2^d*(TraceStaticRow.gateTable hF hw hp base f st r k' d).cells :=
  rfl

@[simp] theorem count_hidden (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' d : ℕ) :
    (network hF hw hp base st hs hf r k' d).internal = TraceUniformRow.SharedCount w p r k' d f +
      2^d*(TraceStaticRow.gateTable hF hw hp base f st r k' d).internal := rfl

/-- The native record decoder can use its ordinary zero-guard descriptor
compiler on the compressed S-pin network. Only public port-source
addresses are restricted; the repeated small gate table is identical. -/
theorem network_eq_guarded (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' d : ℕ) :
    network hF hw hp base st hs hf r k' d =
      GuardedNetwork.network (e:=0) (TraceStaticRow.gateTable hF hw hp base f st r k' d)
        (fun v j => relabel bitPin (TraceStaticRow.portSource hw hs hf base v
          ((Fintype.equivFin (TraceStaticRow.Port w p r k' d)).symm j)))
        (fun _ => Fin.elim0) (fun _ => Fin.elim0) := by
  rw [network,TraceStaticRow.network,restrict_assemble,GuardedNetwork.zero_guards]

/-- The low bit of header word i belongs to row i/2. Neighboring inputs in
positions 2j and 2j+1 are the two tracks of exactly the same physical site. -/
noncomputable def rawLayout (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' : ℕ)
    (fit : S+f ≤ 2^(1+(k+low))) :
    RowLayout (network hF hw hp base st hs hf r k' (k+low)) k low (1+((k+low)+(k+low)))
      (TraceStaticRow.gateTable hF hw hp base f st r k' (k+low)).cells := by
  let L := TraceStaticRow.layout hF hw hp base st hs hf r k' fit
  let owner := fun i : Fin S => L.pinRow (finProdFinEquiv (i,(⟨0,by omega⟩ : Fin w)))
  apply restrictLayout L bitPin owner
  intro i j he
  obtain ⟨⟨a,b⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [bitPin,Equiv.symm_apply_apply] at he
  split at he
  · rename_i h
    obtain rfl := Option.some.inj he
    have hb : b = (⟨0,by omega⟩ : Fin w) := Fin.ext h
    exact congrArg (fun z => L.pinRow (finProdFinEquiv (a,z))) hb.symm
  · cases he

noncomputable def layout (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' : ℕ)
    (fit : S+f ≤ 2^(1+(k+low))) :
    RowLayout (network hF hw hp base st hs hf r k' (k+low)) k low (1+((k+low)+(k+low)))
      (TraceStaticRow.gateTable hF hw hp base f st r k' (k+low)).cells :=
  (rawLayout hF hw hp base st hs hf r k' fit).canonical

theorem layout_pin (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' : ℕ)
    (fit : S+f ≤ 2^(1+(k+low))) (i : Fin S) :
    ((layout hF hw hp base st hs hf r k' fit).pinRow i).val = i.val/2 := by
  change ((TraceStaticRow.layout hF hw hp base st hs hf r k' fit).pinRow
    (finProdFinEquiv (i,(⟨0,by omega⟩ : Fin w)))).val = _
  rw [TraceStaticRow.layout_pin,Equiv.symm_apply_apply]


/-- The incoming and outgoing pins of every interleaved external
coordinate have the same owner for the chronological matrix scan. -/
theorem paired_pins (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k' : ℕ)
    (fit : S+f ≤ 2^(1+(k+low))) (i : ℕ) (hi : 2*i+1 < S) :
    (layout hF hw hp base st hs hf r k' fit).pinRow ⟨2*i,by omega⟩ =
      (layout hF hw hp base st hs hf r k' fit).pinRow ⟨2*i+1,hi⟩ := by
  apply Fin.ext
  simp only [layout_pin]
  omega

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
