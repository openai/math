import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Fetch the prior signed outgoing mark for each old-halo candidate -/
namespace Hierarchy.DescentOrdinarySignedMeta.MarkGather
open DescentSIMDLookup DescentSharedCableNames DescentOrdinaryAtomFieldRAM.ROM DescentPackedColony DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def flag {D cap : ℕ} (newRole : Bool) (x : Option (Stage.Live D cap)) : Cell 1 :=
  ((x.any (fun old=>newRole || old.markedOut)).toNat:Cell 1)

def kernel (D cap : ℕ) (newRole : Bool) (x : Cell (DescentSignedCableCodec.width D cap)) (_ : Cell 0) :=
  flag newRole (DescentSignedCableCodec.decode D cap x)

theorem encode_ghost (D cap : ℕ) : DescentSignedCableCodec.encode (D:=D) (cap:=cap) none=0 := by
  have pair (a b : ℕ) : DescentSignedCableCodec.pair a b (0,0)=0 := by apply Fin.ext; rfl
  have bits : DescentSignedCableCodec.bits false false=0 := rfl
  simp [DescentSignedCableCodec.encode,Packed.token,bits,pair]; rfl

theorem empty (D cap : ℕ) (newRole : Bool) : kernel D cap newRole 0 0=0 := by
  change flag newRole (DescentSignedCableCodec.decode D cap 0)=0
  rw [←encode_ghost D cap,DescentSignedCableCodec.decode_encode]
  rfl

def pages (D cap M : ℕ) : Fin (2+2)→Page := Fin.addCases (binary (kernel D cap false) M) (binary (kernel D cap true) M)
def width (D cap M : ℕ) := DescentSignedCableCodec.width D cap*M
def stop (base D cap M : ℕ) := base+4*2^width D cap M
def locations (newRole : Bool) : Fin 2→Fin (2+2) := if newRole then Fin.natAdd 2 else Fin.castAdd 2
def lut (base D cap M : ℕ) (newRole : Bool) :=
  joined (pages D cap M) (width D cap M) base (locations newRole)

theorem page_bits (D cap M : ℕ) (j : Fin (2+2)) : (pages D cap M j).bits=width D cap M := by
  fin_cases j <;> simp [pages,binary,width,Fin.addCases]

/-- This read has the same cost at every old path, including a missing donor. -/
theorem work {P : ℕ} (base D cap M H : ℕ) (newRole : Bool)
    (ports : Ports P) (prior : Bank) (path : Fin P) :
    ((lut base D cap M newRole).read (peerExpr ports prior H path) (.lit 0)).work=57 := by
  rw [DescentPackedZip.work]
  rfl

/-- All eleven roles share these four fixed short pages. The previous bank is
the actual outgoing first-grain signed-handle column. A duplicated halo path
or an empty handle yields a zero bit, including at unfilled SIMD lanes. -/
theorem issued_on {w D cap H G M P : ℕ} (base : ℕ) (ports : Ports P) (prior : Bank)
    (R : Fin H→Fin P→Option (Fin H)) (path : Fin P) (newRole : Bool)
    (panel : Fin H→Fin G→Option (Stage.Live D cap)) (m : Memory w)
    (room : stop base D cap M<2^w) (access : Accessible ports prior H G M w base)
    (routing : Mounted ports R m G M)
    (stored : Reads prior (fun v g=>DescentSignedCableCodec.encode (panel v g)) M m) :
    let pg:=pages D cap M
    let bits:=width D cap M
    let dst:=after pg bits base m
    let source:=(lut base D cap M newRole).read (peerExpr ports prior H path) (.lit 0)
    (mount pg bits w base).Exec m dst (4+10*(4*2^bits)) ∧
      source.Fits w (stop base D cap M) ∧ Source source (fun v g=>flag newRole
        ((R v path).bind (fun donor=>panel donor g))) M dst := by
  intro pg bits dst source
  let e:=peerExpr ports prior H path
  let x:=fun v g=>(R v path).elim 0 (fun donor=>DescentSignedCableCodec.encode (panel donor g))
  have fitE : e.Fits w base := peer_fits ports prior base access path
  have got : Source e x M m := peerSource ports prior base access _ m routing _ stored path
  have held : Source e x M dst := fun r=>(ProtocolRAM.eval_below e _ m dst fitE (fun a ha=>
    DescentOrdinaryAtomFieldRAM.ROM.frame pg bits base m a (.inl ha))).trans (got r)
  have bf (i : Fin (2+2)) : (bank pg bits base i).Fits w (stop base D cap M) :=
    bank_room pg bits base _ i (page_bits _ _ _ i).le le_rfl room
  have guard : Fits (lut base D cap M newRole) e (.lit 0) (DescentSignedCableCodec.width D cap) 0 M (stop base D cap M) w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) fitE,trivial,bf _,bf _,
      by exact page_bits _ _ _ _,by
        rw [Nat.add_zero]
        exact page_bits D cap M (locations newRole 1)⟩
  have trueROM : Static (lut base D cap M newRole) (kernel D cap newRole) M dst :=
    binary_mounted _ M pg bits base m (fun j=>(page_bits _ _ _ j).le) (locations newRole)
      (fun j => by
        cases newRole
        · exact Fin.addCases_left j
        · exact Fin.addCases_right j)
  have zero : Source (.lit 0) (fun _ : Fin H=>fun _ : Fin G=>(0:Cell 0)) M dst := by
    intro p
    change 0=(((finFunctionFinEquiv (fun i : Fin M=>if _:p.2.val*M+i.val<G then (0:Cell 0) else 0)).val:ℕ):Word w)
    simp []
  refine ⟨DescentStaticWordColumn.mount base _ _ m room,?_,?_⟩
  · change ((lut base D cap M newRole).read e (.lit 0)).Fits w (stop base D cap M)
    simp [Tables.read,Expr.Fits,guard.left,guard.shift,guard.apply]
  · have read:=read_data _ e (.lit 0) _ guard _ (empty _ _ _) dst trueROM x _ held zero
    convert read using 1
    funext v g
    cases step:R v path with
    | none => simp [x,step,empty,flag]
    | some donor => simp [x,step,kernel]

end
end Hierarchy.DescentOrdinarySignedMeta.MarkGather

end OAI
