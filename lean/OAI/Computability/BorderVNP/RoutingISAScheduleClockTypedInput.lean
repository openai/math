import OAI.Computability.BorderVNP.CellSparseExteriorTyped
import OAI.Computability.BorderVNP.RoutingISATypedBudget

/-! # Physical typed directory sources after sparse exterior encoding -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse CellPacket CellPacketEncode

/-- The live frame, seven-word sources and argument allocation at the typed
initializer. The stored cell input here uses the physical exterior encoding. -/
structure TypedDirectoryInput {w : ℕ} (pub : Arg → Word w) (m : Memory w) (table count n : ℕ)
    (tasks : ℕ → TypedBatch.Task) (cells : ℕ → CellInput) : Prop where
  /-- The last frame operand fits in a word. -/
  frame : (pub 0).val+90 < 2^w
  /-- The published width is this machine's word width. -/
  width : (m ((pub 0).val+30)).val=w
  /-- The native task table starts at the specified base. -/
  base : (m ((pub 0).val+89)).val=table
  /-- The native table contains exactly the specified owned rows. -/
  length : (m ((pub 0).val+90)).val=count
  /-- Each of the seven source words of each task is addressable. -/
  space : table+7*count ≤ 2^w
  /-- Every typed task has disjoint argument and publication regions. -/
  allocated : TypedBatch.Allocated w table count tasks
  /-- Both its header and its variable argument sections occur at the input addresses. -/
  stored : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m
  /-- The call and compact data addresses fit. -/
  room : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w
  /-- Each selected row names its actual physical payload and fits the burst cap. -/
  placed : TypedBatch.PlacedRows pub m tasks count n cells
  /-- Owner words and directory frame survive typed publication. -/
  control : TypedBatch.ControlLayout pub m tasks count

/-- The actual sparse writer image supplies each rewritten typed row and its
encoded payload. The root frame and original owner words survive, so the
same compact row witnesses apply at the private call directory. -/
theorem typedDirectory_of_sparseImage {w n : ℕ} (pub : Arg → Word w) (m mt : Memory w)
    (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned) (original : ℕ → TypedBatch.Task)
    (D : ℕ → Directory) (privateWires : ℕ → ℕ) (external : ℕ → SparseExterior.Field)
    (fp : (pub 0).val=l.frame) (loaded : l.Loaded (readings m)) (frame : l.frame+92 < 2^w)
    (post : readings mt=SparseExterior.written l owned (readings m) l.count)
    (clearRows : SparseExterior.Protected l owned original) (width : readings m (l.frame+30)=w)
    (prior : ∀ i < l.count, (original i).Stored m l.tasks i ∧
      WordsAt (readings m) (original i).cell.descriptorBase (descriptors (original i).cell.chunks) ∧
      ∀ c ∈ (original i).cell.chunks, c.Stored (readings m))
    (registers : ∀ i < l.count, ∀ k ∈ [0,14,15,30,89,90], (owned i).Outside l i (l.frame+k))
    (owners : ∀ i < l.count, ∀ j < (Frame.ofMemory pub m).count, (owned i).Outside l i ((Frame.ofMemory pub m).address j)) :
    let tasks := fun i => (owned i).typed l (original i)
    let f := Frame.ofMemory pub m
    l.tasks+7*l.count ≤ 2^w → TypedBatch.Allocated w l.tasks l.count tasks →
    (∀ j < l.count, (tasks j).callRow+2 < 2^w ∧ (tasks j).cell.Room w) → TypedBatch.ControlLayout pub m tasks l.count →
    (∀ i < f.count, readings m (f.address i)=f.team → ∃ j < l.count, (original j).callRow=f.address i ∧
      (original j).cell.packet=Packet.bits (D i) (privateWires i) ∧ (owned j).field=external i) →
    (∀ j < l.count, ((tasks j).cell.burst w).length ≤ TeamScales.width n (1/2)) →
    TypedDirectoryInput pub mt l.tasks l.count n tasks (fun i => ⟨D i,privateWires i,(external i).bytes⟩) ∧
      Frame.ofMemory pub mt=f ∧ (∀ i < f.count, mt (f.address i)=m (f.address i)) := by
  intro tasks f space allocation room control ordinals cap
  have unchanged (a : ℕ) (clear : ∀ i < l.count, (owned i).Outside l i a) : mt a=m a := by
    apply Fin.ext
    change readings mt a = readings m a
    rw [post]
    exact SparseExterior.written_preserve l owned (readings m) (i:=0) (Nat.zero_le _) a (fun j _ hj => clear j hj)
  have fld (k : ℕ) (hk : k ∈ [0,14,15,30,89,90]) : mt ((pub 0).val+k)=m ((pub 0).val+k) :=
    unchanged _ (fun i hi => fp ▸ registers i hi k hk)
  have ff : Frame.ofMemory pub mt=f := by
    simp only [f,Frame.ofMemory,show mt (pub 0).val=m (pub 0).val from fld 0 (by decide),fld 14 (by decide),fld 15 (by decide)]
  have own (i : ℕ) (hi : i < f.count) : mt (f.address i)=m (f.address i) :=
    unchanged _ fun j hj => owners j hj i hi
  have live : ∀ i < l.count, (tasks i).Stored mt l.tasks i ∧ (tasks i).cell.Stored mt := by
    intro i hi
    obtain ⟨row,desc,chunks⟩ := prior i hi
    exact SparseExterior.stored_after l owned original m mt post clearRows i hi row desc chunks
  have ctl : TypedBatch.ControlLayout pub mt tasks l.count := ⟨control.frame,fun j hj i hi => by
    rw [ff] at hi ⊢; exact control.owners j hj i hi⟩
  have placed : TypedBatch.PlacedRows pub mt tasks l.count n (fun i => ⟨D i,privateWires i,(external i).bytes⟩) := by
    refine ⟨?_,cap⟩
    intro i hi belongs
    rw [ff] at hi belongs ⊢
    rw [own i hi] at belongs
    obtain ⟨j,hj,address,packet,field⟩ := ordinals i hi belongs
    refine ⟨j,hj,address,?_⟩
    rw [←field]
    exact (owned j).typed_payload l (original j) (D i) (privateWires i) packet
  refine ⟨⟨by rw [fp]; omega,?_,?_,?_,space,allocation,live,room,placed,ctl⟩,ff,own⟩
  · rw [fld 30 (by decide),fp]; exact width
  · rw [fld 89 (by decide),fp]; exact loaded.tasks
  · rw [fld 90 (by decide),fp]; exact loaded.count

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
