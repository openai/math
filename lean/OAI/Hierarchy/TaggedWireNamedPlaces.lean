import OAI.Hierarchy.TaggedWireSiteBits
import OAI.Hierarchy.TaggedWireNativeSlot
import OAI.Hierarchy.ProbePlacedTerm

namespace OAI
/-! # Immutable bit placements for positive and zero-width original rows -/

noncomputable section
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe CalendarTape Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators

variable {S n : ℕ} (ends : Fin n→Chord S) (bits : Fin n→ℕ)

def key (i : Fin n) := Fintype.equivFin (Chord S) (ends i)

theorem measured (e : Chord S) :
    NativeSlot.mass (key ends) bits (Fintype.equivFin _ e)=installedWidths ends bits e := by
  simp [NativeSlot.mass,key,installedWidths,Finsupp.finsetSum_apply,unitChord,Finsupp.single_apply,eq_comm]

/-- Every original row keeps its own interval of bits on a parallel chord.
The number of earlier bits is computed on the original row ordinals. -/
def chordBits : Bundle bits ≃ Σe:Chord S,Fin (installedWidths ends bits e) :=
  let e := Fintype.equivFin (Chord S)
  let rename := Equiv.sigmaCongrLeft (β:=fun j=>Fin (NativeSlot.mass (key ends) bits j)) e
  (NativeSlot.put (key ends) bits).trans <| rename.symm.trans
    (Equiv.sigmaCongrRight fun ch=>finCongr (measured ends bits ch))

theorem chord_at (q : Bundle bits) : (chordBits ends bits q).1=ends q.1 := by
  change (Fintype.equivFin (Chord S)).symm (key ends q.1)=ends q.1
  exact (Fintype.equivFin _).symm_apply_apply _

/-- One actual bit offset within the mixed-width chord word for an
original row, using the exact mixed-radix order used by rowBits. -/
def sourceBit (q : Bundle bits) : Fin (installedWidths ends bits (ends q.1)) :=
  Fin.cast (congrArg (installedWidths ends bits) (chord_at ends bits q)) (chordBits ends bits q).2

theorem offset (q : Bundle bits) : (chordBits ends bits q).2.val=
    TaggedShorterCommonScan.earlier (key ends) bits q.1.val (key ends q.1)+q.2.val := by
  let e := Fintype.equivFin (Chord S)
  let mass := NativeSlot.mass (key ends) bits
  let p := NativeSlot.put (key ends) bits q
  let rename := Equiv.sigmaCongrLeft (β:=fun j => Fin (mass j)) e
  let c := rename.symm p
  have slot : c.2.val = p.2.val :=
    congrArg (fun z : Bundle mass => z.2.val) (rename.apply_symm_apply p)
  exact slot

/-- Attach the same bit to either of its two actual sites. This bijection
covers also every ambient chord of width zero (which has no bit). -/
def sides (U : Widths S) : ((Σe:Chord S,Fin (U e)) × Bool) ≃ Σs,SiteBit U s where
  toFun t := ⟨(portGraph S).vertex t.1.1 t.2,⟨⟨(t.1.1,t.2),rfl⟩,t.1.2⟩⟩
  invFun v := (⟨v.2.1.1.1,v.2.2⟩,v.2.1.1.2)
  left_inv := by rintro ⟨⟨e,i⟩,s⟩; rfl
  right_inv := by rintro ⟨_,⟨⟨⟨e,s⟩,rfl⟩,i⟩⟩;rfl

def halfBits : Bundle bits × Bool ≃ Σs,SiteBit (installedWidths ends bits) s :=
  ((chordBits ends bits).prodCongr (Equiv.refl _)).trans (sides _)

theorem half_site (q : Bundle bits) (b : Bool) :
    (halfBits ends bits (q,b)).1=(portGraph S).vertex (ends q.1) b := by
  change (portGraph S).vertex (chordBits ends bits q).1 b=_
  rw [chord_at]

variable {H : Type} (port : Fin n × Bool ↪ H) (cap : H→ℕ)
variable (room : ∀j b,bits j≤cap (port (j,b)))

def role : Bundle bits × Bool ↪ (Σu:H,Fin (cap u)) where
  toFun p := ⟨port (p.1.1,p.2),p.1.2.castLE (room p.1.1 p.2)⟩
  inj' := by
    rintro ⟨⟨j,v⟩,a⟩ ⟨⟨l,w⟩,b⟩ eq
    have t := port.injective (congrArg Sigma.fst eq)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj t
    have val : v.val=w.val := congrArg (fun z : Σu:H,Fin (cap u)=>z.2.val) eq
    obtain rfl := Fin.ext val
    rfl

/-- Every party/state bit is sent to its own original physical port.
Changing another row's width leaves these public per-port positions fixed. -/
def place : (Σs,SiteBit (installedWidths ends bits) s) ↪ (Σu:H,Fin (cap u)) :=
  (halfBits ends bits).symm.toEmbedding.trans (role bits port cap room)

theorem read (q : Bundle bits) (b : Bool) :
    place ends bits port cap room (halfBits ends bits (q,b)) =
      ⟨port (q.1,b),q.2.castLE (room q.1 b)⟩ := by simp [place,role]; rfl

theorem owned (site : H→Fin S) (fixed : ∀j b,site (port (j,b))=(portGraph S).vertex (ends j) b)
    (a : Σs,SiteBit (installedWidths ends bits) s) : site (place ends bits port cap room a).1=a.1 := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (halfBits ends bits).surjective a
  rw [read,half_site]
  exact fixed _ _

theorem unique (a b : Σs,SiteBit (installedWidths ends bits) s) :
    place ends bits port cap room a=place ends bits port cap room b ↔ a=b :=
  (place ends bits port cap room).injective.eq_iff

abbrev LiveEnd := {p : Fin n×Bool // 0<bits p.1}

def live {H : Type} (ports : LiveEnd bits ↪ H) (caps : H→ℕ) (fits : ∀p,bits p.val.1≤caps (ports p)) :
    Bundle bits × Bool ↪ (Σu:H,Fin (caps u)) where
  toFun q :=
    let r : LiveEnd bits := ⟨(q.1.1,q.2),Nat.zero_lt_of_lt q.1.2.isLt⟩
    ⟨ports r,q.1.2.castLE (fits r)⟩
  inj' := by
    rintro ⟨⟨j,v⟩,a⟩ ⟨⟨l,w⟩,b⟩ eq
    have t := congrArg Subtype.val (ports.injective (congrArg Sigma.fst eq))
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj t
    have val : v.val = w.val := congrArg (fun z : Σu:H,Fin (caps u)=>z.2.val) eq
    obtain rfl := Fin.ext val
    rfl

/-- Padded header addresses, including an arbitrary self-loop, need no public
port identity. Positive rows keep their literal original relative order. -/
def livePlace {H : Type} (ports : LiveEnd bits ↪ H) (caps : H→ℕ) (fits : ∀p,bits p.val.1≤caps (ports p)) :=
  (halfBits ends bits).symm.toEmbedding.trans (live bits ports caps fits)

def transport {K : ℕ} {A B : Widths K} (same : A=B) :
    (Σs,SiteBit A s)≃(Σs,SiteBit B s) := by subst B;exact Equiv.refl _

def transportAt {K : ℕ} {A B : Widths K} (same : A=B) {s : Fin K} :
    SiteBit A s→SiteBit B s := by subst B;exact id

theorem transport_pair {K : ℕ} {A B : Widths K} (same : A=B) {s : Fin K} (a : SiteBit A s) :
    transport same ⟨s,a⟩=⟨s,transportAt same a⟩ := by subst B;rfl

theorem transport_site {K : ℕ} {A B : Widths K} (same : A=B) (a : Σs,SiteBit A s) :
    (transport same a).1=a.1 := by subst B;rfl

end Hierarchy.WireTelescope.NamedAperture
end

end OAI
