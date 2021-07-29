/* Object
 * Author: Veronica
 * Creation date: 2021/6/30
 */
MACHINE
    Object
SEES
    Tag
SETS
    OBJ;
    STATUS = {Free,Full}
VARIABLES
    obj,oid,otag ,status
INVARIANT
    obj ⊆ OBJ ∧
    oid ∈ obj → NAT1 ∧
    otag ∈ obj → TAG ∧
    status ∈ obj → STATUS
INITIALISATION
    obj , oid , otag, status := {},{} ,{},{}
OPERATIONS
    Init_Obj(oo1,oid1,oo2,oid2,oo3,oid3,oo4,oid4) =
    PRE
        oo1 ∈ OBJ ∧
        oo1 ∉ obj ∧
        oo2 ∈ OBJ ∧
        oo2 ∉ obj ∧
        oo3 ∈ OBJ ∧
        oo3 ∉ obj ∧
        oo4 ∈ OBJ ∧
        oo4 ∉ obj ∧
        oo1 ≠ oo2 ∧
        oo3 ≠ oo4 ∧
                oid1 ∈ ℕ₁ ∧
        oid1 ∉ ran(oid) ∧
        oid2 ∈ ℕ₁ ∧
        oid2 ∉ ran(oid) ∧
        oid3 ∈ ℕ₁ ∧
        oid3 ∉ ran(oid) ∧
        oid4 ∈ ℕ₁ ∧
        oid4 ∉ ran(oid)
    THEN
        obj := obj ∪ {oo1,oo2,oo3,oo4} ||
        oid := oid ∪ {oo1 ↦ oid1,oo2 ↦ oid2,oo3 ↦ oid3,oo4 ↦ oid4} ||
        otag := otag ∪ {oo1 ↦ NU,oo2 ↦ NS,oo3 ↦ TU,oo4 ↦ TS} ||
        status := status ∪ {oo1 ↦ Free ,oo2 ↦ Free ,oo3 ↦ Free ,oo4 ↦ Free}
    END;
    Add_Obj(oo,ii,tt,ss) =
    PRE
        oo ∈ OBJ ∧
        oo ∉ obj ∧
        ii ∈ NAT1 ∧
        ii ∉ ran(oid) ∧
        tt ∈  TAG ∧
        ss ∈ STATUS
    THEN
        obj := obj ∪ {oo} ||
        oid := oid ∪ {oo ↦ ii} ||
        otag := otag ∪ {oo ↦ tt} ||
        status := status ∪ {oo ↦ ss}
    END;
    Del_Obj(oo) =
    PRE
        oo ∈ OBJ ∧
        oo ∈ obj 
        
    THEN
        obj := obj - {oo} ||
        oid := {oo} ◀ oid ||
        otag := {oo} ◀ otag ||
        status := {oo} ◀ status
    END;
    Change_Obj_Status(oo1,ss1,oo2,ss2) =
    PRE
        oo1 ∈ obj ∧
        ss1 ∈ STATUS ∧
                oo2 ∈ obj ∧
        ss2 ∈ STATUS
    THEN
         status := status ⋖ {oo1 ↦ ss1,oo2 ↦ ss2}
         
    END;
    Update_Obj_Tag(oo,tt)=
    PRE
        oo ∈ obj ∧
                tt ∈ TAG ∧
                oo ↦ tt ∉ otag
    THEN
        otag(oo) := tt
    END
END
