/* Subject
 * Author: Veronica
 * Creation date: 2021/5/6
 */
MACHINE
    Sub   
SEES
    Tag
SETS
    SUB ;
    EXE_STATE = {Ready,Run,Blocked,Final};
    AC_STATE = {Pre,Wait,Acing,Post}
VARIABLES
    sub,SID,sid,stag,exe_state,ac_state
INVARIANT
    sub ⊆ SUB ∧
        SID ⊆ ℕ₁ ∧
    sid ∈ sub → SID ∧
    stag ∈ sub → TAG ∧
    exe_state ∈ sub → EXE_STATE ∧
    ac_state ∈ sub → AC_STATE
INITIALISATION
    sub ,SID,sid ,stag,exe_state,ac_state := {} , {} , {} , {} , {} ,{}
OPERATIONS
    Create_Sub(ss,ii,tt,exe,ac) =
    PRE
       ss ∈ SUB ∧
       ss ∉ sub ∧       
       ii ∈ ℕ₁ ∧
              ii ∉ ran(sid) ∧ 
               tt  ∈ TAG ∧
               exe ∈ EXE_STATE ∧
               ac ∈ AC_STATE
    THEN
       sub := sub ∪ {ss} ||
       sid := sid ∪ {ss ↦ ii} ||
       stag := stag ∪ {ss ↦ tt} ||
       exe_state := exe_state ∪ {ss ↦ exe} ||
       ac_state := ac_state ∪ {ss ↦ ac}
   END;
   Delete_Sub(ss) =
    PRE
       ss ∈ SUB ∧
       ss ∈ sub 
    THEN
       sub := sub - {ss} ||
       sid := {ss} ◀ sid ||
       stag := {ss} ◀ stag ||
       exe_state := {ss} ◀ exe_state ||
       ac_state := {ss} ◀ ac_state
   END;
   Change_Sub_State(ss,exe,ac) =
   PRE
       ss ∈ sub∧
            exe ∈ EXE_STATE ∧
            ac ∈ AC_STATE
   THEN
        exe_state(ss) := exe ||
        ac_state(ss) := ac
    END;
    Change_Sub_Tag(ss,tt) = 
    PRE
        ss ∈ sub ∧
                tt ∈ TAG
    THEN
        stag(ss) := tt
    END
    
    
END
