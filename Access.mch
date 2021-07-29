/* Access
 * Author: Veronica
 * Creation date: 2021/7/28
 */
MACHINE
    Access
SEES
    Tag
INCLUDES
    Subject,Object,Policy
SETS
    DT = {SYS,SYS_EXIT,TSYS,TSYS_EXIT,TUENTER,TULEAVE,TSENTER,TSLEAVE,NULL}
VARIABLES
    ready_sub,run_sub,blocked_sub,sub_obj,sub_ac_obj,ac_flag,ac_policy_flag,sub_next_obj,ac_event,dtrans,next_obj
INVARIANT
    ready_sub ⊆ sub ∧
      run_sub ⊆ sub ∧
       blocked_sub ⊆ sub ∧
       sub_obj ∈ sub ↔ obj ∧
       sub_ac_obj ∈ sub ⇸ obj ∧
       sub_next_obj ∈ sub ⇸ obj ∧
       next_obj ∈ sub ⇸ obj ∧
       ac_flag ∈ 0..1 ∧
       ac_policy_flag ∈ 0..1 ∧
       ac_event ∈ OP ∧
       dtrans ∈ DT
   INITIALISATION
       ready_sub := {} || run_sub := {} || blocked_sub := {} || sub_obj := {} ||sub_ac_obj := {} || sub_next_obj := {} ||
       ac_flag,ac_policy_flag := 0,0 || ac_event := Nop || dtrans := NULL || next_obj := {}
   OPERATIONS
       Init_Env(ss,sid1,oo1,oid1,oo2,oid2,oo3,oid3,oo4,oid4) =
       PRE
           ss ∈ SUB ∧
                      ss ∉ sub ∧
                      sid1 ∈ ℕ₁ ∧
                      sid1 ∉ ran(sid) ∧
                      oo1 ∈ OBJ ∧
           oo1 ∉ obj ∧
           oo2 ∈ OBJ ∧
           oo2 ∉ obj ∧
           oo3 ∈ OBJ ∧
           oo3 ∉ obj ∧
           oo4 ∈ OBJ ∧
           oo4 ∉ obj ∧
                     oid1 ∈ ℕ₁ ∧
                     oid1 ∉ ran(oid) ∧
                     oid2 ∈ ℕ₁ ∧
           oid2 ∉ ran(oid) ∧
                     oid3 ∈ ℕ₁ ∧
           oid3 ∉ ran(oid) ∧
                     oid4 ∈ ℕ₁ ∧
           oid4 ∉ ran(oid)
       THEN
           Create_Sub(ss,sid1,NU,Ready,Pre)||
           Init_Obj(oo1,oid1,oo2,oid2,oo3,oid3,oo4,oid4)
       END;
       
       Domain_Trans(ss,dt) =
       PRE
           ss ∈ run_sub ∧
                      dt ∈ DT - {NULL} ∧
                      dtrans =NULL
       THEN
           dtrans := dt
       END;
       
       Update_Tag(ss,oo,tt) =
       PRE
            ss ∈ run_sub ∧
                        oo ∈ obj ∧
                        tt ∈ TAG ∧
                        stag(ss) ↦ otag(oo) ∈ update_policy ∧//当前主体模式下的客体标签是可更新的
            stag(ss) ↦ tt ∈ update_policy //当前主体模式下欲更新的标签是策略允许的
       THEN
            Update_Obj_Tag(oo,tt)
       END;
       Judge_ac_policy(ss,oo,ac)=
       PRE
           ss ∈ ready_sub ∪ run_sub ∧
           oo ∈ obj ∧
           ac ∈ OP ∧
                     ac_flag = 0 ∧
            ac_policy_flag = 0 ∧
                        ac ∈ OP - {Nop} ∧
                        ac_event = Nop ∧
                        next_obj = {}
       THEN
           IF 
               stag(ss) ↦ otag(oo) ↦ ac ∈ ac_policy
           THEN
               ac_policy_flag := 1 ||
                ac_event := ac ||
               next_obj(ss) := oo 
           ELSE
               ready_sub := ready_sub - {ss} ||
               run_sub := run_sub - {ss} ||
               blocked_sub := blocked_sub ∪ {ss} ||
               Change_Sub_State(ss,Final,Post)
            END
       END;
   
       Sub_Ac_Obj(ss,oo)=
       PRE
           ss ∈ sub ∧
                    exe_state(ss) ∈ {Ready,Run,Blocked} ∧
                       ac_flag = 0 ∧
            ac_policy_flag = 1 ∧
                        oo ∈ obj ∧
                        ss ↦ oo ∈ next_obj 
       THEN
               IF
                   status(oo) = Free
               THEN
                   ac_flag := 1 ||
                   run_sub := run_sub ∪ {ss} ||
                   ready_sub := ready_sub - {ss} ||
                   blocked_sub := blocked_sub - {ss} ||
                   Change_Sub_State(ss,Run,Acing) ||
                   sub_next_obj(ss) := next_obj(ss) ||
                   next_obj := {}
               ELSE
                   ready_sub := ready_sub - {ss} ||
               run_sub := run_sub - {ss} ||
               blocked_sub := blocked_sub ∪ {ss} ||
               Change_Sub_State(ss,Blocked,Wait)
               END
       END;
       
       Change_Status(ss)=
       PRE
           ss ∈ run_sub ∧
                       ac_event ∈ OP - {Nop} ∧
                      ac_flag = 1 ∧
            ac_policy_flag = 1 ∧
                        {ss} ◁ sub_next_obj ≠ {}
       THEN
            ac_flag := 0 ||
            ac_policy_flag := 0 ||
            IF 
                {ss} ◁ sub_ac_obj ≠ {}
            THEN
                  Change_Obj_Status(sub_ac_obj(ss),Free,sub_next_obj(ss),Full) ||
                  sub_ac_obj(ss) := sub_next_obj(ss)
            ELSE
                  Change_Obj_Status(sub_next_obj(ss),Full,sub_next_obj(ss),Full) ||
                  sub_ac_obj(ss) := sub_next_obj(ss)
            END ||
            sub_next_obj := {ss} ◀ sub_next_obj||
            ac_event := Nop     
       END;
       
       Quit_Ac_Obj(ss) = 
       PRE
           ss ∈ run_sub ∧
                      {ss} ◁ sub_ac_obj ≠ {} ∧
                      ac_flag = 0 ∧
                      ac_policy_flag = 0 ∧
                      ac_event = Nop
       THEN
           sub_ac_obj := {ss} ◀ sub_ac_obj ||
           Change_Obj_Status(sub_ac_obj(ss),Free,sub_ac_obj(ss),Free)
       END
END
