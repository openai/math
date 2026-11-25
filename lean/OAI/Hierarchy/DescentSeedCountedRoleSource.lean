import OAI.Hierarchy.DescentSeedSourceExtent
import OAI.Hierarchy.DescentSeedExteriorVote
import OAI.Hierarchy.DescentSeedWideBundleRead

namespace OAI
/-! # Reading the real original ballot census after the wide validator -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL DescentPackedSeed DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
variable {F T : Type} [Field F] {k p e j r t : ℕ} (X : Approximation F k p) (R s h w : ℕ)
  (sel : Select X R s → T) (lo C grain : ℕ) (ss : List (Source T))
  (origin : ℕ) (ex : Fin e → Plane j r → Fin t → Bool) (z : T ⊕ Hidden e j r t → Bool)
set_option quotPrecheck false
local notation "O" => Fintype.card (Old X)
local notation "A" => DescentPackedSeed.Primitive.pieces h s
local notation "n" => DescentPackedSeed.rows X R s h
local notation "flag" => DescentWideSeedFlags.endInput X R s h
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "raw" => widePackedImage X R s h w sel lo C grain ss origin ex z
local notation "counted" => DescentWideSeedFlags.countedAt X R s h sel (z∘Sum.inl)

theorem counted_role_source (m : Memory w)
    (fixed : ∀a < origin+17*DescentExteriorShelf.span j r t e,m a=(raw) a) (wide : 16*digitsNeeded s ≤ h)
    (fit : flag+(n+1) < 2^w) (separate : flag+(n+1) ≤ lo) (booked : lowEnd ≤ origin) :
    let source:=publicWords X
    let jobs:=DescentPackedSeed.Primitive.Source.jobs X R s h
    source+DescentDyadicSpan.span jobs ≤ flag ∧
      ∀u : Row O R A,(counted) m (source+(row O R A u).val)=
        ((data (DescentPackedSeed.Primitive.bundles X ((z∘Sum.inl)∘sel)) u).val:Word w) :=by
  intro source jobs
  have table:=role_source_table X R s h wide
  have dictEnd : (DescentWideSeedFlags.dictionary X R s h).base ≤ flag:=Nat.le_add_right ..
  have lowLo : lo ≤ lowEnd :=
    calc
      lo ≤ lo + extent grain ss := Nat.le_add_right ..
      _ ≤ (DescentPackedProfileInstall.dict (lo + extent grain ss) C grain).base :=
        Nat.le_add_right ..
      _ ≤ lowEnd := Nat.le_add_right ..
  have keep:=(wideCounted_on X R s h w sel lo C grain ss origin ex z m fixed (by omega) fit separate booked).2.2.2.2
  refine ⟨table.trans dictEnd,?_⟩
  intro u
  let addr:=source+(row O R A u).val
  have small : addr < source+DescentDyadicSpan.span jobs :=
    Nat.add_lt_add_left ((row O R A u).isLt.trans_le (DescentDyadicSpan.span_ge jobs)) _
  have inTable := small.trans_le table
  have inCheck :=inTable.trans_le dictEnd
  have inLo : addr < lo:=by omega
  have inBook:=inLo.trans_le lowLo
  have full : addr < origin+17*DescentExteriorShelf.span j r t e:= (inBook.trans_le booked).trans_le (Nat.le_add_right ..)
  calc
    (counted) m addr=m addr :=keep _ (.inl inCheck)
    _=(raw) addr:=fixed _ full
    _=wideOriginal X R s h w sel lo C grain ss (z∘Sum.inl) addr :=
      widePacked_original X R s h w sel lo C grain ss origin ex z booked inBook
    _=DescentWideSeedFlags.initial X R s h w sel (z∘Sum.inl) addr :=
      DescentPackedEpochShelves.frame lo C grain ss (z∘Sum.inl)
        (DescentWideSeedFlags.initial X R s h w sel (z∘Sum.inl)) (a:=addr) inLo
    _=_:=(DescentWideSeedFlags.lower X R s h w sel (z∘Sum.inl) inTable).trans
      (DescentPackedSeed.Primitive.wide_from_header X h w wide _ u)

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
