/* Mem
 * Author: Veronica
 * Creation date: 2021/5/19
 */
MACHINE
    Mem
SETS
    MEM;TAG={N_tag,TU_tag,TC_tag,TS_tag}; STATUS = {Free,Full} ; UPDATE = {Updated, Updating}//memory tag 

VARIABLES
    mem,MID,mid,mtag,mstatus
INVARIANT
    mem ⊆MEM &
    MID ⊆ NAT1 &
    mid ∈ mem --> MID &
    mtag ∈ mem -->TAG &
    mstatus ∈ mem  --> STATUS
INITIALISATION
    mem,MID,mid,mtag,mstatus:={},{},{},{},{}
OPERATIONS
    Init_Mem(mm1,ii1,mm2,ii2,mm3,ii3)=
    	PRE
	mm1 ∈ MEM ∧
        mm1 ∉ mem ∧
        mm2 ∈ MEM ∧
        mm2 ∉ mem ∧
        mm3 ∈ MEM ∧
        mm3 ∉ mem ∧
	mm1 ≠ mm2 ∧
	mm2 ≠ mm3 ∧
	mm1 ≠ mm3 ∧
	ii1 ∈ NAT1 ∧
	ii2 ∈ NAT1 ∧
	ii3 ∈ NAT1 ∧
	ii1 ≠ ii2 ∧
	ii2 ≠ ii3 ∧
	ii1 ≠ ii3 ∧	
	ii1 ∉ MID ∧
	ii2 ∉ MID ∧
	ii3 ∉ MID
    THEN
        mtag := mtag ∪ {mm1 ↦ N_tag} ∪ {mm2 ↦ TC_tag} ∪ {mm3 ↦ TS_tag} ||
	MID := MID ∪ {ii1,ii2,ii3} ||
	mid := mid ∪ {mm1 ↦ ii1 , mm2 ↦ ii2 , mm3 ↦ ii3}||
        mem := mem ∪ {mm1,mm2,mm3}||
	mstatus := mstatus ∪ {mm1 ↦ Free } ∪ {mm2 ↦ Free } ∪ {mm3 ↦ Free}
    END;
    
    Add_Mem(mm,ii,tag)=
    PRE
        mm ∈ MEM ∧
        mm ∉ mem ∧
	ii ∈ NAT1 ∧
	ii ∉ MID ∧
        tag ∈ TAG
    THEN
	mem := mem ∪ {mm}||
	MID := MID ∪ {ii} ||
	mid(mm) := ii || 
        mtag(mm) := tag ||
	mstatus := mstatus ∪ { mm ↦ Free}
    END;
    
    Del_Mem(mm)=//this mm is a set
    PRE
        mm ⊆ mem 
    THEN
	mem := mem - mm||
	MID := MID - mid[mm]||
        mtag := mm ◀ mtag ||
	mid := mm ◀ mid ||
        mstatus :=mm ◀ mstatus
    END;

    Change_Mem_Status(mm1,ss1,mm2,ss2)=
    PRE
	mm1 ∈ mem ∧
	ss1 ∈ STATUS ∧
	mm2 ∈ mem ∧
	ss2 ∈ STATUS
    THEN
	IF
		ss1 = ss2 ∧
		mm1 = mm2
	THEN 
		mstatus := mstatus ⋖ {mm1 ↦ ss1 ,mm2 ↦ ss2}
	ELSIF
		mm1 ≠ mm2

	THEN
		mstatus := mstatus ⋖ {mm1 ↦ ss1 ,mm2 ↦ ss2}
	END
    END;

    Tag_Updating(mm,tag) =
    PRE
	mm ∈ mem ∧
	tag ∈ TAG 
    THEN
	mtag(mm) := tag
    END

END
