import OAI.Hierarchy.DescentDatedPrimitiveUpdate
import OAI.Hierarchy.DescentOrdinaryPalettePosted

namespace OAI
/-! Selected archive words from the previous primitive, donor chip, true stamp and old halo directory. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
  (A : ArgumentEntry v) («matching» : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
local notation "L" => v.paletteShape
local notation "src" => v.primitiveSources floor A «matching» radix
local notation "oldEnd" => v.operandEnd floor
local notation "base" => v.primitiveFirst oldEnd
local notation "G" => v.gadget
local notation "s" => v.palette.seedWidth
local notation "Z" => v.palette.grainLimit
local notation "op" => v.palette.rotor

def paletteStock (past : Fin (L).blocks→Fin (L).hosts→Fin (L).oldGroups→Cell ((L).primitiveBits*(L).oldNodes))
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (hosts : (L).hosts=v.bornBook.hosts) (groups : (L).oldGroups=v.bornBook.groups)
    (origin : Fin (L).blocks→Fin (L).successors→Fin (L).groups→Cell ((L).originBits*(L).newNodes))
    (next : Fin (L).hosts→Fin (L).ports→Option (Fin (L).hosts)) : (L).Stock where
  previous:=past
  newborn j h g:=DescentOrdinaryPaletteBirth.published G s Z op v.bornBook
    (j.cast (show (L).fields=DescentOrdinaryPaletteBirth.fields v.bornBook from by
      change 2^v.reference.k*v.reference.capacity*6=v.bornBook.blocks*v.bornBook.cap*6
      rw [«matching».newBlocks,«matching».newCap])) (chip (h.cast hosts) (g.cast groups))
  origin:=origin
  next:=next

variable {w : ℕ}
set_option maxHeartbeats 1200000 in
theorem primitive_read (fits : v.PrimitiveRoom floor A w) (size : (L).Capacity src)
    (past : Fin (L).blocks→Fin (L).hosts→Fin (L).oldGroups→Cell ((L).primitiveBits*(L).oldNodes))
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (hosts : (L).hosts=v.bornBook.hosts) (groups : (L).oldGroups=v.bornBook.groups)
    (origin : Fin (L).blocks→Fin (L).successors→Fin (L).groups→Cell ((L).originBits*(L).newNodes))
    (next : Fin (L).hosts→Fin (L).ports→Option (Fin (L).hosts)) (m : Memory w)
    (previous : ∀x,Reads ((src).previous x) (past x) (L).priorLanes m)
    (mass : v.bornBook.rows≤(A.chipBank v floor).size)
    (donor : Reads (A.chipBank v floor) chip v.bornBook.lanes m)
    (ranks : ∀x,Reads ((src).origin x) (origin x) (L).originLanes m)
    (ports : ∀h i,m ((src).halo.base+(h.val*(L).ports+i.val))= (DescentPackedColony.target (next h i):Word w))
    (x : Fin (L).blocks) :
    let S:=v.paletteStock floor A «matching» past chip hosts groups origin next
    Reads (v.primitiveBank oldEnd x) (S.output x) v.palette.nextLanes
      ((v.primitiveUpdate floor A «matching» radix w).image m):=by
  intro S
  have early : oldEnd≤base:=(DescentOrdinaryPaletteBirth.order v.bornBook oldEnd).1.trans
    (DescentOrdinaryPaletteBirth.order v.bornBook oldEnd).2
  have finish : base≤(L).roof base:=by rw [(L).translated]; exact Nat.le_add_right ..
  have room:=finish.trans_lt fits.space
  let out:=(v.primitiveBirth floor A w).image m
  have carry (a : ℕ) (ha : a<oldEnd) : out a=m a:=
    (DescentOrdinaryPaletteBirth.any G s Z op v.bornBook (A.chipBank v floor) oldEnd m fits.chip room).2 a (.inl ha)
  have got:=DescentOrdinaryPaletteBirth.posted G s Z op v.bornBook (A.chipBank v floor) oldEnd m fits.chip chip mass donor room
  have cast_read {a H J H' J' M : ℕ} (hh : H=H') (hg : J=J') (b : Bank) (f : Fin H'→Fin J'→Cell a)
      (prior : Reads b f M out) : Reads b (fun h g=>f (h.cast hh) (g.cast hg)) M out:=by
    subst H';subst J';exact prior
  have observed : (L).Observed src S out:=by
    refine ⟨fun x=>Layout.carry_reads (fits.past _) (size.past x) carry (previous x),?_,
      fun x=>Layout.carry_reads (fits.origin _) (size.origin x) carry (ranks x),?_⟩
    · intro t
      have count : (L).fields = DescentOrdinaryPaletteBirth.fields v.bornBook := by
        change 2^v.reference.k * v.reference.capacity * 6 = v.bornBook.blocks * v.bornBook.cap * 6
        rw [«matching».newBlocks, «matching».newCap]
      let index := t.cast count
      let cell := fun h g => DescentOrdinaryPaletteBirth.published G s Z op v.bornBook index (chip h g)
      exact cast_read hosts groups (DescentOrdinaryPaletteBirth.bank v.bornBook oldEnd index)
        cell (got index)
    · intro h i
      have pick:=Layout.before_bank fits.halo (finProdFinEquiv (h,i)) fits.cells
      exact (carry _ (by simpa only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm, primitiveSources] using pick)).trans (ports h i)
  have ready : (L).Early base src w:=
    ⟨fun _=>Layout.widen early (fits.past _),fun _=>(DescentOrdinaryPaletteBirth.placed v.bornBook oldEnd room _).1,
      fun _=>Layout.widen early (fits.origin _),Layout.widen early fits.halo,fits.cells⟩
  exact (L).posted base src ready size S out observed fits.space x

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
