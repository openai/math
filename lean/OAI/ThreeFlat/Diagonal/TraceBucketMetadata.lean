import OAI.ThreeFlat.Diagonal.TraceBucketInitial

namespace OAI
/-! # The local history generator's four words for each bucket row -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex
open RAM RAM.BitLayout
open scoped Classical
open private both rows from OAI.ThreeFlat.Diagonal.LaneInitialNetwork
variable {F : Type*} [CommSemiring F] {p k low o c r H : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o c} {lane : Lane (k+1)} (I : BucketIndex P lane)

omit [CommSemiring F] in
private theorem attach_ext (q : Fin I.x) : (I.attach (r:=r) (q.castAdd _)).val=q.val := by
  simp only [attach,initialSource,ports,bank,both,rows,arity,Fin.append_right,Fin.append_left,Fin.val_castAdd]

omit [CommSemiring F] in
private theorem attach_send (t : Fin I.t) :
    (I.attach (r:=r) (Fin.natAdd I.x (t.castAdd I.t))).val=
      I.x+(selected (r:=r) P.mask (I.tag t).1 (0:Fin (k+1))).val*I.t+t.val := by
  simp only [attach,initialSource,ports,bank,both,rows,arity,Fin.append_right,Fin.append_left]
  simp [finProdFinEquiv]; ac_rfl

omit [CommSemiring F] in
private theorem attach_recv (t : Fin I.t) :
    (I.attach (r:=r) (Fin.natAdd I.x (Fin.natAdd I.t t))).val=
      I.x+bank r I.t+(selected (r:=r) P.mask (I.tag t).1 (Fin.last k)).val*I.t+t.val := by
  simp only [attach,initialSource,ports,bank,both,rows,arity,Fin.append_right]
  simp [finProdFinEquiv]; ac_rfl

private abbrev rett (I : BucketIndex P lane) := (RelayNetwork.network (F:=F) (r:=r) I.tag P.mask (0:Fin (k+1))).cells

private noncomputable def remap (A : BitNetwork.Rectangular.Address I.h H) (s : BitSource I.h I.arity) :=
  TraceBucketJoin.mount (I.attach (r:=r)) id (BitNetwork.Rectangular.move I.network A s)

theorem remap_translate (A : BitNetwork.Rectangular.Address I.h H) (s : BitSource N.internal p) :
    sourceAddress (I.remap (r:=r) A (I.translate s)) = I.translateWord (r:=r) A s := by
  cases s with
  | constant v => rfl
  | pin j =>
    by_cases h : (splitRow _ _ (P.pinRow j)).1=lane <;>
      simp [remap,translate,translateWord,h,TraceBucketJoin.mount,BitNetwork.Rectangular.move,
        sourceAddress,attach_ext]
  | hidden j =>
    by_cases h : (splitRow _ _ (P.hiddenRow j)).1=lane <;>
      simp [remap,translate,translateWord,h,TraceBucketJoin.mount,BitNetwork.Rectangular.move,
        sourceAddress,hiddenBase]

theorem metadata_original (A : BitNetwork.Rectangular.Address I.h H)
    (tag : ((Fin 3 → Bool)→F)→ℕ) (i : Fin I.c) (j : Fin 4) :
    HistoryCompiledRows.metadata tag (I.firstNetwork (r:=r) A 0)
      (Fin.natAdd (rett (r:=r) I) ((i.castAdd I.t).castAdd H)) j=I.original (r:=r) tag i j := by
  by_cases hj : j.val<3
  · simp only [HistoryCompiledRows.metadata,original,hj,dite_true]
    simp only [firstNetwork,TraceBucketJoin.network,rett,BitNetwork.Rectangular.network,network,
      Fin.append_right,Fin.append_left]
    change sourceAddress (I.remap (r:=r) A (I.argumentSource i ⟨j.val,hj⟩))=_
    by_cases wired : LaneCursor.wired (N.source (I.cell i).val ⟨j.val,hj⟩)
    · simp only [argumentSource,wired,dite_true,remap,BitNetwork.Rectangular.move,
        TraceBucketJoin.mount,sourceAddress,attach_recv]
      omega
    · simp only [argumentSource,wired,dite_false,remap,BitNetwork.Rectangular.move,
        TraceBucketJoin.mount,sourceAddress]
      cases h : N.source (I.cell i).val ⟨j.val,hj⟩ with
      | constant b => rfl
      | pin i => simp [h,LaneCursor.wired] at wired
      | hidden i => simp [h,LaneCursor.wired] at wired
  · simp [HistoryCompiledRows.metadata,original,hj,firstNetwork,TraceBucketJoin.network,
      BitNetwork.Rectangular.network,network]

theorem metadata_compare (A : BitNetwork.Rectangular.Address I.h H)
    (tag : ((Fin 3 → Bool)→F)→ℕ) (i : Fin I.t) (j : Fin 4) :
    HistoryCompiledRows.metadata tag (I.firstNetwork (r:=r) A 0)
      (Fin.natAdd (rett (r:=r) I) ((Fin.natAdd I.c i).castAdd H)) j=I.compareRow (r:=r) A tag i j := by
  fin_cases j
  · simp [HistoryCompiledRows.metadata,firstNetwork,TraceBucketJoin.network,BitNetwork.Rectangular.network,
      rett,Fin.append_right,Fin.append_left,network,testSource,compareRow,TraceBucketJoin.mount,BitNetwork.Rectangular.move,sourceAddress,attach_send]
    omega
  · simp only [HistoryCompiledRows.metadata,firstNetwork,TraceBucketJoin.network,rett,
      BitNetwork.Rectangular.network,network,Fin.append_right,Fin.append_left]
    change sourceAddress (I.remap (r:=r) A (I.emission (I.tag i)))=_
    unfold compareRow
    simp only [one_ne_zero,ite_false,ite_true,emission,emissionWord]
    cases h : I.probe (I.tag i) with
    | none => rfl
    | some a => exact I.remap_translate A (N.source a.val.1 a.val.2)
  · simp [HistoryCompiledRows.metadata,firstNetwork,TraceBucketJoin.network,rett,
        BitNetwork.Rectangular.network,network,Fin.append_right,Fin.append_left,testSource,compareRow,
        TraceBucketJoin.mount,BitNetwork.Rectangular.move,sourceAddress]
  · simp [HistoryCompiledRows.metadata,firstNetwork,TraceBucketJoin.network,BitNetwork.Rectangular.network,
      network,compareRow]

theorem metadata_hole (A : BitNetwork.Rectangular.Address I.h H)
    (tag : ((Fin 3 → Bool)→F)→ℕ) (q : Fin H) (j : Fin 4) :
    HistoryCompiledRows.metadata tag (I.firstNetwork (r:=r) A 0)
      (Fin.natAdd (rett (r:=r) I) (Fin.natAdd (I.c+I.t) q)) j=I.holeRow (r:=r) A tag q j := by
  by_cases hj : j.val<3 <;>
    simp [HistoryCompiledRows.metadata,firstNetwork,TraceBucketJoin.network,BitNetwork.Rectangular.network,
      rett,network,Fin.append_right,BitNetwork.Rectangular.checkSource,BitNetwork.Rectangular.isHole,holeRow,hj,
      TraceBucketJoin.mount,sourceAddress,hiddenBase]

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
