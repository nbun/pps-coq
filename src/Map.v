Definition totalMap (K V : Type) := K -> V.

Definition partialMap (K V : Type) := totalMap K (option V).

Definition emptyTMap {K V : Type} (v : V) : totalMap K V := fun _ => v.

Definition emptyPMap {K V : Type} : partialMap K V := emptyTMap None.

Definition updateTMap {K V : Type} (beq : K -> K -> bool)
                      (m : totalMap K V) (k : K) (v : V) :=
  fun k' => if beq k k' then v else m k'.

Definition updatePMap {K V : Type} (beq : K -> K -> bool)
                      (m : partialMap K V) (k : K) (v : V) :=
  updateTMap beq m k (Some v).