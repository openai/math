import OAI.Hierarchy.TaggedWireDatedTurnStart
import OAI.Hierarchy.ProtocolRAMTurnShelf
import OAI.Hierarchy.TaggedWireTurnOffsets

namespace OAI
/-! # Bounds on the actual five dated spill words, including parallel chords -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open scoped Classical BigOperators

variable {K n edges r rows : ℕ}

theorem datedBase_room (ends : Fin n→Chord K) (bits : Fin n→ℕ)
    (i : Fin n) (_on : 0<bits i) :
    datedBase ends bits i+bits i≤ installedWidths ends bits (ends i) := by
  rw [datedBase,← NativeSlot.next,←NamedAperture.measured,←NativeSlot.full]
  exact NativeSlot.earlier_mono _ _ _ i.isLt

/-- Every bit of this chord belongs to an actual row interval. This converse
lets a differently numbered genuine row table pay the complete chord width. -/
theorem installed_le_of_datedBase (ends : Fin n→Chord K) (bits : Fin n→ℕ) (cap : ℕ)
    (fits : ∀i,0<bits i→datedBase ends bits i+bits i≤cap) (ch : Chord K) :
    installedWidths ends bits ch≤cap := by
  by_contra! tooMany
  let x : Bundle bits:=(NamedAperture.chordBits ends bits).symm ⟨ch,⟨cap,tooMany⟩⟩
  have numeral : (NamedAperture.chordBits ends bits x).2.val=cap :=
    congrArg (fun r : Σc,Fin (installedWidths ends bits c)=>r.2.val)
      ((NamedAperture.chordBits ends bits).apply_symm_apply ⟨ch,⟨cap,tooMany⟩⟩)
  have offset : (NamedAperture.chordBits ends bits x).2.val=datedBase ends bits x.1+x.2.val :=
    NamedAperture.offset ends bits x
  have own:=x.2.isLt
  have limit:=fits x.1 ((Nat.zero_le _).trans_lt own)
  omega

variable (old : Fin n→Chord K) (edge : Fin edges→Chord K) (route : Fin n→List (Fin edges))
  (bits : Fin n→ℕ) (ord : Fin r≃Σi,Fin (route i).length)
local notation "mass" => routeLoad route bits

/-- Starting at the strict same-chord prefix, the entire positive source interval
fits on that chord. At a paid occurrence the additional native rank still leaves
room for the full interval, including repeated visits to the same paid edge. -/
theorem datedStart_room (cap : ℕ) (oldCap : ∀e,installedWidths old bits e≤cap)
    (newCap : ∀e,installedWidths edge mass e≤cap)
    (i : Fin n) (on : 0<bits i) (ref : TurnRef) :
    datedStart old edge route bits ord i ref+bits i≤cap := by
  have source:=(datedBase_room old bits i on).trans (oldCap _)
  rcases ref with b|⟨j,b⟩
  · simpa only [datedStart,refRole,refStart,Nat.add_zero] using source
  · by_cases hj : j<(route i).length
    · let t : Fin (route i).length:=⟨j,hj⟩
      let e:=(route i).get t
      have used : NativeSlot.start route bits ord i t+bits i≤ mass e :=
        NativeSlot.start_room route bits ord i t on
      have live : 0< mass e := by omega
      have physical:=(datedBase_room edge mass e live).trans (newCap _)
      simp only [datedStart,refRole,refStart,dite_eq_left hj]
      change datedBase edge mass e+NativeSlot.start route bits ord i t+bits i≤cap
      omega
    · simp only [datedStart,refRole,refStart,dite_eq_right hj,Nat.zero_add]
      omega

private theorem refRole_room (before : Fin n→Bool→ℕ) (after : Fin edges→Bool→ℕ)
    {M : ℕ} (positive : 0<M) (low : ∀i b,before i b<M) (high : ∀i b,after i b<M) (i : Fin n) (ref : TurnRef) :
    refRole route before after i ref<M := by
  rcases ref with b|⟨j,b⟩
  · exact low i b
  · by_cases hj : j<(route i).length
    · simpa only [refRole,dite_eq_left hj] using high ((route i).get ⟨j,hj⟩) b
    · simpa only [refRole,dite_eq_right hj] using positive

/-- The bit decoder and the native RAM see the same whole signed role, absolute
chord offset and positive width on every retained seat. -/
theorem dated_fields_fit (p e W : ℕ) (col : Fin rows→Fin 7→ℕ)
    (item : Fin rows→Fin n) (ref : Fin rows→Bool→TurnRef)
    (before : Fin n→Bool→ℕ) (after : Fin edges→Bool→ℕ)
    (width : ∀i,col i 4=bits (item i))
    (roles : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)=refRole route before after (item u.val) (ref u.val b))
    (starts : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)=datedStart old edge route bits ord (item u.val) (ref u.val b))
    (oldCap : ∀c,installedWidths old bits c≤2^e) (newCap : ∀c,installedWidths edge mass c≤2^e)
    (roleRoom : ∀i b,before i b< min (2^p) (2^W)) (paidRoom : ∀i b,after i b< min (2^p) (2^W))
    (addressRoom : 2^e≤2^W) (weightRoom : ∀i,bits i<2^W) :
    (∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W) ∧
    (∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p) ∧
    ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e := by
  have code (u : ProtocolRAMTurnShelf.Live col) (b : Bool) :
      col u.val (if b then 1 else 0)< min (2^p) (2^W) := by
    rw [roles]
    exact refRole_room route before after (lt_min (Nat.two_pow_pos _) (Nat.two_pow_pos _)) roleRoom paidRoom _ _
  have interval (u : ProtocolRAMTurnShelf.Live col) (b : Bool) :
      col u.val (if b then 3 else 2)+col u.val 4≤2^e := by
    rw [starts,width]
    exact datedStart_room old edge route bits ord _ oldCap newCap _ (by rw [←width];exact Nat.pos_of_ne_zero u.property) _
  refine ⟨?_,fun u b=>(code u b).trans_le (min_le_left ..),interval⟩
  intro u f
  have on:=Nat.pos_of_ne_zero u.property
  have address (b : Bool) : col u.val (if b then 3 else 2)<2^W:=by
    have within:=interval u b
    omega
  fin_cases f
  · exact (code u false).trans_le (min_le_right ..)
  · exact (code u true).trans_le (min_le_right ..)
  · exact address false
  · exact address true
  · change col u.val 4 < 2^W
    rw [width u.val]
    exact weightRoom (item u.val)


end Hierarchy.WireTelescope

end
end OAI
