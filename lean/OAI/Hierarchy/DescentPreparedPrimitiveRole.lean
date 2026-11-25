import OAI.Hierarchy.DescentPrimitiveGuardedRoots
import OAI.Hierarchy.DescentIssuedMatrixPacket

namespace OAI
/-! # Read the original gate selector from its four authentic prepared input families -/
namespace Hierarchy.DescentPrimitiveBirth
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHostDirectory DescentIssuedRotorRoles
open DescentResetHostSize
open DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentResetGates DescentSharedLeafLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r n hw D field bit cap : ℕ}
local notation "L" => 2^r
local notation "N" => DescentRotorWindowArchive.count D L cap

def priorFields (matrix : Fin N→Cell field) (cap₀ level flag : Cell field)
    (i : Fin (guardInputs D L cap)) :=
  (finSumFinEquiv.symm i).elim
    (fun j=>(finSumFinEquiv.symm j : Fin N⊕Fin 1).elim matrix (fun _=>cap₀))
    (fun j : Fin 2=>if j=0 then level else flag)

theorem prior_level (matrix : Fin N→Cell field) (cap₀ level flag : Cell field) :
    flagPart (D:=D) («L»:=L) (cap:=cap) (priorFields (D:=D) (r:=r) (cap:=cap) matrix cap₀ level flag) 0=level:=by
  simp [flagPart,priorFields]
theorem prior_sample (matrix : Fin N→Cell field) (cap₀ level flag : Cell field) :
    flagPart (D:=D) («L»:=L) (cap:=cap) (priorFields (D:=D) (r:=r) (cap:=cap) matrix cap₀ level flag) 1=flag:=by
  simp [flagPart,priorFields]

variable (src : RootSources D (2^r) cap) (board : NonlinearExpanders.Graph n hw)
    (packet f Ht C groupDigits batches layerBits : ℕ) (primitive : CanonicalTag (2^n)→Cell bit)
    (H factor hubBits : ℕ) (neighbors hubs : Bank) (start G M cmp : ℕ)
    (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr) (bookPage : RootPage r (2^n))
local notation "B" => src.reserved (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    H factor hubBits neighbors hubs start G M cmp pair bookPage

theorem actual_guard_row (side : Bool) (root : Code r) (gate : Fin (2^n)) (i : Fin (guardInputs D L cap)) :
    (((B).good side root (.inr gate)).2.reads i)=
      (finSumFinEquiv.symm i).elim
        (fun j=>(finSumFinEquiv.symm j : Fin N⊕Fin 1).elim (((B).good side root (.inl false)).2.reads) (fun _=>src.priorCap))
        (fun j : Fin 2=>if j=0 then src.relativeDepth else src.self (DescentRotorRootPresence.sample root)):=rfl

theorem actual_guard_law (side : Bool) (root : Code r) (gate : Fin (2^n)) (x : Fin (guardInputs D L cap)→Cell field) :
    ((B).good side root (.inr gate)).2.law (encode field _ x)=
      guarded (D:=D) («L»:=L) (cap:=cap) n r packet f groupDigits batches layerBits primitive side root.val gate x:=by
  change guarded _ _ _ _ _ _ _ _ _ _ _ ((encode field _).symm (encode field _ x))=_
  rw [Equiv.symm_apply_apply]

variable {w : ℕ}
theorem prior_sensors (side : Bool) (root : Code r) (gate : Fin (2^n)) (m : Memory w)
    (matrix : Fin H→Fin G→Fin N→Cell field) (cap₀ level flag : Fin H→Fin G→Cell field)
    (mx : ∀i,Source (((B).good side root (.inl false)).2.reads i) (fun h g=>matrix h g i) M m)
    (cp : Source src.priorCap cap₀ M m) (dp : Source src.relativeDepth level M m)
    (kd : Source (src.self (DescentRotorRootPresence.sample root)) flag M m)
    (i : Fin (guardInputs D L cap)) :
    Source (((B).good side root (.inr gate)).2.reads i)
      (fun h g=>priorFields (D:=D) (r:=r) (cap:=cap) (matrix h g) (cap₀ h g) (level h g) (flag h g) i) M m:=by
  rw [actual_guard_row]
  unfold priorFields
  cases finSumFinEquiv.symm i with
  | inl j=>
    simp only [Sum.elim_inl]
    cases (finSumFinEquiv.symm j : Fin N⊕Fin 1) with
    | inl k=>exact mx k
    | inr _=>exact cp
  | inr j=>by_cases h:j=0 <;>simp only [Sum.elim_inr,h,ite_true,ite_false] <;>assumption

/-- The reserved matrix and the good role use the identical mounted lower
memory. Unlike an exceptional page no later scalar counting pass intervenes. -/
theorem issued_original {previous K R hh ll t c oldGroups : ℕ}
    (a : Receiver D cap previous n r c H oldGroups K R M hh ll t field Ht w)
    (pitch : G=2^c) (space : a.PreparedFits (B)) (original : Memory w)
    (side : Bool) (root : Code r) (gate : Fin (2^n))
    (matrix : Fin H→Fin G→Fin N→Cell field) (cap₀ level flag : Fin H→Fin G→Cell field)
    (mx : ∀i,Source (((B).good side root (.inl false)).2.reads i) (fun h g=>matrix h g i) M (a.preparedMid (B) space original))
    (cp : Source src.priorCap cap₀ M (a.preparedMid (B) space original))
    (dp : Source src.relativeDepth level M (a.preparedMid (B) space original))
    (kd : Source (src.self (DescentRotorRootPresence.sample root)) flag M (a.preparedMid (B) space original))
    (held : ∀i,(((B).good side root (.inr gate)).2.reads i).Fits w
      ((RootTemplates.arena (a.headerEnd (B)) H (2^c) M r n D).middle ((rootIndex r (2^n) (side,.inl (root,.inr gate))).val)))
    (short : M*max (field*guardInputs D L cap) (bit*batches)≤w/2) (pos : 0<M)
    (floor : ℕ) (later : Memory w) (past : a.preparedEnd (B)≤floor) (room : floor<2^w)
    (frame : ∀j,j<floor→later j=a.preparedImage (B) space original j) :
    Source (.lookup (guardBank (a.headerEnd (B)) H (2^c) M r n D (side,.inl (root,.inr gate))) .row)
      (fun h g=>guarded (D:=D) («L»:=L) (cap:=cap) n r packet f groupDigits batches layerBits primitive side root.val gate
        (priorFields (D:=D) (r:=r) (cap:=cap) (matrix h g) (cap₀ h g) (level h g) (flag h g))) M later:=by
  let book:=(B)
  subst G
  let words:=fun h g=>priorFields (D:=D) (r:=r) (cap:=cap) (matrix h g) (cap₀ h g) (level h g) (flag h g)
  have old:=prior_sensors src board packet f Ht C groupDigits batches layerBits primitive H factor hubBits neighbors hubs
    start (2^c) M cmp pair bookPage side root gate (a.preparedMid book space original) matrix cap₀ level flag mx cp dp kd
  have read:=prior_guard a book space original (side,.inl (root,.inr gate)) floor past room words held short pos old later frame
  change Source _ (fun h g => ((book.good side root (.inr gate)).2.law
    (encode field (guardInputs D L cap) (words h g)))) M later at read
  have laws : (fun h g => (book.good side root (.inr gate)).2.law
      (encode field (guardInputs D L cap) (words h g))) =
      (fun h g => guarded (D:=D) («L»:=L) (cap:=cap) n r packet f groupDigits batches layerBits
        primitive side root.val gate (words h g)) := by
    funext h g
    exact actual_guard_law src board packet f Ht C groupDigits batches layerBits primitive H factor
      hubBits neighbors hubs start (2^c) M cmp pair bookPage side root gate (words h g)
  rw [laws] at read
  exact read

end
end Hierarchy.DescentPrimitiveBirth

end OAI
