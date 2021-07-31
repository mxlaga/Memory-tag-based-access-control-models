
MACHINE
    MTAC
SEES
    Tag
INCLUDES
    Sub,Obj,Policy
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
    dtrans ∈ DT ∧
    sub_ac_obj ⊆ sub * obj ∧ ∀(ss,oo). (ss ∈ sub ∧ oo ∈ obj ∧ oo = sub_ac_obj(ss) ⇒ stag(ss) ↦ otag(oo) ∈ dom(ac_policy) )∧
    ∀ ss.(ss ∈ sub  ⇒ sub_ac_obj(ss) ∈ ran({ss} ◁ sub_obj))∧
    dom(sub_ac_obj) ⊆ ac_state⁻¹[{Acing}] ∧
    dom(dom(ac_policy)) ⊆ TAG ∧ ran(dom(ac_policy)) ⊆ TAG ∧ ran(ac_policy) ⊆ OP ∧
    ∀(ss,oo).(ss ∈ dom(sub_ac_obj)∧ oo ∈ obj ∧ oo = sub_ac_obj(ss) ⇒ stag(ss) ↦ otag(oo) ∈ dom(ac_policy)) ∧
    ∀ ss. (ss ∈ run_sub ∧ stag(ss) ∈ {NU,TU} ⇒ (sub_ac_obj(ss) ∈ ran({ss} ◁ sub_obj))) ∧             
    ∀ ss. (ss ∈ run_sub ∧ stag(ss) = NU ⇒ (otag(sub_ac_obj(ss)) ∈ {NU})) ∧
    ∀ ss. (ss ∈ run_sub ∧ stag(ss) = NS ⇒ (otag(sub_ac_obj(ss)) ∈ {NU,NS})) ∧
    ∀ ss. (ss ∈ run_sub ∧ stag(ss) = TU ⇒ (otag(sub_ac_obj(ss)) ∈ {NU,NS,TU})) ∧
    ∀ ss. (ss ∈ run_sub ∧ stag(ss) = TS ⇒ (otag(sub_ac_obj(ss)) ∈ {NU,NS,TU,TS})) ∧
    status[sub_ac_obj[run_sub]] ⊆ {Full} ∧
    status[sub_next_obj[run_sub]] ⊆ {Free} ∧
    run_sub ∪ ready_sub ∪ blocked_sub = sub ∧
    run_sub ∩ ready_sub ∩ blocked_sub = ∅ 
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
                        stag(ss) ↦ otag(oo) ∈ up_policy ∧//当前主体模式下的客体标签是可更新的
            stag(ss) ↦ tt ∈ up_policy //当前主体模式下欲更新的标签是策略允许的
       THEN
            Update_Obj_Tag(oo,tt)
       END;

       Judge_Ac_Policy(ss,oo,ac)=
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
   
       Judge_Status(ss,oo)=
       PRE
           ss ∈ sub ∧
	   oo ∈ obj ∧
	   ss ↦ oo ∈ next_obj ∧
           exe_state(ss) ∈ {Ready,Run,Blocked} ∧
           ac_flag = 0 ∧
           ac_policy_flag = 1                                            
       THEN
               IF
                   status(oo) = Free
               THEN
                   ready_sub := ready_sub - {ss} ||
		   run_sub := run_sub ∪ {ss} ||
                   blocked_sub := blocked_sub - {ss} ||
		   ac_flag := 1 ||
                   Change_Sub_State(ss,Run,Acing) ||
                   sub_next_obj(ss) := next_obj(ss) ||
                   next_obj := {}
               ELSE
                   ready_sub := ready_sub - {ss} ||
               		  run_sub := run_sub - {ss} ||
                   blocked_sub := blocked_sub ∪ {ss} ||
                   Change_Sub_State(ss,Blocked,Wait) ||
		   sub_next_obj := {ss}◀sub_next_obj ||
		   sub_ac_obj := {ss}◀sub_ac_obj
               END
       END;
       
       Sub_Ac_Obj(ss)=
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
