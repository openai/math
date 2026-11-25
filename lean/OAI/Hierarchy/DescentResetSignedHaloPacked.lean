import OAI.Hierarchy.DescentResetSignedHaloMatrix
import OAI.Hierarchy.DescentPackedHostLookupROM

namespace OAI
/-! # A single resident lookup for all previous signed neighbor queries -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentSIMDLookup DescentPackedZip DescentSortedRoster DescentResetOriginHaloRAM
open DescentPackedChildNeighbor.SIMD DescentPackedChildNeighbor.SIMD.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H D S N w a b G M : ℕ}

theorem rank_bound (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (h : Fin H) (j : Fin (D+1)) :
    rank p home h j≤D+2:=by
  unfold rank
  split
  next here=>
    let v:=home ⟨h.val,here⟩
    have subset : present (closed p) v⊆Finset.univ.image (fun i : Fin (D+1)=>(closed p v i).getD v):=by
      intro t inSet
      obtain ⟨i,same⟩:=(Finset.mem_filter.mp inSet).2
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [same]⟩
    have card := (Finset.card_le_card subset).trans Finset.card_image_le
    have card' : (present (closed p) v).card≤D+1:=by simpa using card
    have low:=Finset.card_filter_le (s:=present (closed p) v) (·<((closed p v j).getD v))
    exact Nat.succ_le_succ (low.trans card')
  next=>omega

def short (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (h : Fin H) (j : Fin (D+1)) : Cell b:=rank p home h j

/-- A lookup on the immutable previous host can be performed before compacting the next host rectangle. -/
theorem old_rank (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (i : Fin N) (hi : N≤H) (j : Fin (D+1)) :
    rank p id (home i) j=rank p home (i.castLE hi) j:=by
  simp [rank,i.isLt,(home i).isLt]

theorem old_lookup (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (i : Fin N) (hi : N≤H) (q : Cell a) :
    lookup (short (b:=b) p id (home i)) q (List.finRange (D+1))=
      lookup (short (b:=b) p home (i.castLE hi)) q (List.finRange (D+1)):=by
  have equal : short (b:=b) p id (home i)=short (b:=b) p home (i.castLE hi):=by
    funext j
    rw [short,short,old_rank p home i hi j]
  rw [equal]

/-- Every query shares the one installed mask/offset/page book, including different old
ports and different blocks. The label zero selects no donor. -/
theorem packed (matrix : Bank) (base : ℕ) (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (m : Memory w)
    (measured : ∀(h : Fin H) (j : Fin (D+1)),m (matrix.base+(h.val*(D+1)+j.val))=(rank p home h j:Word w))
    (shortRoom : D+2<2^b) (dir : matrix.Fits w base) (capacity : H*(D+1)≤ matrix.size)
    (space : ROM.output base (D+1) a b M H G+H*chunks G M<2^w) :
    let C:=layout base (D+1) a b M (rowBits H G M) matrix
    let stage:=ROM.after base (D+1) a b M H G m
    let top:=ROM.output base (D+1) a b M H G
    (ROM.program base (D+1) a b M H G w).Exec m stage (4+10*ROM.cells (D+1) a b M H G) ∧
    (∀q : Expr,∀x : Fin H→Fin G→Cell a,q.Fits w base→Source q x M m→
      (body C q (List.finRange (D+1))).Fits w top ∧
      Source (body C q (List.finRange (D+1))) (fun h g=>lookup (short (b:=b) p home h) (x h g) (List.finRange (D+1))) M stage) ∧
    (∀z,z<base ∨ base+ROM.cells (D+1) a b M H G≤z→stage z=m z) ∧ CheapCode (ROM.program base (D+1) a b M H G w):=by
  intro C stage top
  have order : base+ROM.cells (D+1) a b M H G≤top:=Nat.le_add_right ..
  have cap : base+ROM.cells (D+1) a b M H G<2^w:=order.trans_lt ((Nat.le_add_right ..).trans_lt space)
  have actual (h : Fin H) (j : Fin (D+1)) : m (matrix.base+(h.val*(D+1)+j.val))=(((short (b:=b) p home h j).val):Word w):=by
    simpa [short,Fin.val_cast_of_lt ((rank_bound p home h j).trans_lt shortRoom)] using measured h j
  have mounted:=ROM.stored (a:=a) (G:=G) (M:=M) matrix base (rowBits H G M) (short (b:=b) p home) m
    ((Nat.add_le_add_left capacity _).trans dir.2.2) actual
  have ret:=DescentStaticWordColumn.frame base (ROM.cells (D+1) a b M H G) (ROM.numbers (D+1) a b M H G) m
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ cap,?_,ret,@DescentStaticWordColumn.cheap _ _ _ _⟩
  intro q x fit got
  have ok:=(ROM.arranged_expr (T:=D+1) (a:=a) (b:=b) (M:=M) (H:=H) (G:=G) matrix q base ⟨dir,capacity⟩
    (ProtocolRAMGeneratedWrite.fits_mono _ ((Nat.le_add_right ..).trans order) fit) space).2
  have carry : Source q x M stage:=fun r=>(ProtocolRAM.eval_below q _ m stage fit (fun z l=>ret z (.inl l))).trans (got r)
  exact ⟨DescentPackedChildNeighbor.SIMD.fitted C q ok (List.finRange (D+1)),measures C q top ok _ stage mounted x carry _⟩

end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
