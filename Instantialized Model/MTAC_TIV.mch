/* MTAC_TIV
 * Author: Veronica
 * Creation date: 2021/4/24
 */
MACHINE
    MTAC_TIV

INCLUDES
    Proc,Mem,Policy
DEFINITIONS //the limition of sets
	scope_PROC == 2;
	scope_MEM == 9;
	/**/MAX_OPERATIONS_Init_Env == 1;
	MAX_OPERATIONS_Init_Proc == 2;
	MAX_OPERATIONS_Create_Enclave == 1;
	MAX_OPERATIONS_Add_Region == 1;
	MAX_OPERATIONS_Add_Data == 1;
	MAX_OPERATIONS_Add_Entries == 1
SETS
	ECB;				//all ECB
	STATES={runable,unrunable};	//all status of enclave
	EID;				//all EID
	ENTRY				//all ENTRY
VARIABLES
    cur_mode,ready_procs,run_proc,blocked_proc,proc_mem,proc_ac_mem,eid,ecb,ecb_mem,ecb_eid,ecb_state,entry,entry_mem,proc_entry,shm_ecb_mem,
load_mem,shm_ecb_eid,TS_flag,shm_ecb,shm_eid,ac_flag,ac_policy_flag,ac_service,proc_next_mem,ac_event ,next_mem,enter_mode

INVARIANT
    	cur_mode ∈ MODE ∧        //the CPU working mode
	enter_mode ∈ MODE ∧
    	ready_procs ⊆ proc ∧     //the processes of ready status
    	run_proc ⊆ proc ∧        //the processes of running status
    	blocked_proc ⊆ proc ∧   //the processes of blocked status
    	proc_mem ∈ proc ↔ mem ∧ //the memories of processes
    	ecb ⊆ ECB ∧             //the ecb header of enclaves
    	eid ⊆ EID ∧              //the eids
	shm_ecb ⊆ ecb ∧             //the ecb header of enclaves
    	shm_eid ⊆ eid ∧              //the eids
    	ecb_mem ∈ ecb ⇸ MEM ∧   //the memory of enclave
    	ecb_eid ∈ ecb ⇸ EID ∧   //the eid of ecbs
    	ecb_state ∈ ecb ⇸ STATES ∧ //the status of ecb
    	entry ⊆ ENTRY ∧    //the entries
    	entry_mem ∈ entry → MEM ∧ //the memory of entries 
   	proc_entry ∈ proc ↔ ENTRY ∧    //the entry of process
    	load_mem ⊆ MEM ∧               // reserve the memory of enclave and entry
    	shm_ecb_mem ∈ shm_ecb → MEM ∧
    	shm_ecb_eid ∈ shm_ecb → EID ∧
   	shm_ecb_eid ∩ ecb_eid={} ∧		//the unique ecb cannot coexist with shm_ecb	
	proc_ac_mem ∈ proc ⇸ mem ∧
	proc_next_mem ∈ proc ⇸ mem ∧
	TS_flag ⊆ 0..1 ∧
	ac_flag ∈ 0..1  ∧  // allow to access  the memory block or not
	ac_policy_flag ∈ 0..1 ∧ // confirm the access policy or not
	ac_service ∈ 0..1 ∧ //access memory or use the services in TS-mode 
	ac_event ∈ OP ∧
	
	next_mem ∈ proc ⇸ mem ∧
	proc_ac_mem ⊆ proc * mem ∧
	dom(proc_ac_mem) ⊆ ac_state⁻¹[{Acing}] ∧	
	dom(dom(ac_policy)) ⊆ MODE ∧ ran(dom(ac_policy)) ⊆ TAG ∧ ran(ac_policy) ⊆ OP ∧
	∀(pp,mm).(pp ∈ dom(proc_ac_mem) ∧ mm ∈ mem ∧ mm = proc_ac_mem(pp) ⇒ pmode(pp) ↦ mtag(mm) ∈ dom(ac_policy)) ∧	
	dom(up_policy)⊆ MODE∧ ran(up_policy) ⊆ TAG∧
	∀ pp.(pp ∈ run_proc ∧ pmode(pp) ∈ {NU,TU} ⇒ (proc_ac_mem(pp) ∈ ran({pp} ◁ proc_mem))) ∧
	∀ pp.(pp ∈ run_proc ∧ pmode(pp) = NU ⇒(mtag(proc_ac_mem(pp))∈{N_tag})) ∧
	∀ pp.(pp ∈ run_proc ∧ pmode(pp) = TU ⇒(mtag(proc_ac_mem(pp))∈{TC_tag,TU_tag,N_tag})) ∧
	∀ pp.(pp ∈ run_proc ∧ pmode(pp) = NS ⇒(mtag(proc_ac_mem(pp))∈{N_tag})) ∧
	∀ pp.(pp ∈ run_proc ∧ pmode(pp) = TS ⇒(mtag(proc_ac_mem(pp))∈{TC_tag,TS_tag,N_tag,TU_tag})) ∧
	mstatus[proc_ac_mem[run_proc]] ⊆ {Full} ∧
	mstatus[proc_next_mem[run_proc]] ⊆ {Free} ∧
	ran(proc_ac_mem) ∩ ran(proc_next_mem) =∅ ∧
	ready_procs ∩ run_proc ∩ blocked_proc = ∅ ∧
	ready_procs ∪ run_proc ∪ blocked_proc = proc
INITIALISATION
    cur_mode:=NU || ready_procs :={} ||run_proc :={}||blocked_proc:={}||proc_mem:={} ||ecb ,ecb_mem,ecb_eid,ecb_state := {},{},{},{} || proc_entry := {}|| entry,entry_mem := {},{} || load_mem :={}||eid :={} || shm_ecb_mem,shm_ecb_eid :={},{} ||TS_flag:={}||shm_ecb,shm_eid:={},{} ||ac_flag,ac_policy_flag,ac_service :=0,0,0 ||  proc_ac_mem := {}||proc_next_mem:={}|| ac_event := Null || next_mem := {} || enter_mode := NU

OPERATIONS
    	Init_Env(mm1,ii1,mm2,ii2,mm3,ii3)=    //Initlize the environment of Sys
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
		ii1 < ii2 ∧
		ii2 < ii3 ∧
		ii3 = 3 ∧
		ii1 ∉ MID ∧
		ii2 ∉ MID ∧
		ii3 ∉ MID ∧
		card(mem)=0
	THEN
        		Init_Mem(mm1,ii1,mm2,ii2,mm3,ii3)||
        		 Create_Ac_Policy
    	END;

    	Init_Proc(pp,ii1,mm,ii2)=					
    	PRE	//processs is initialized and only has N-tag memory
        		pp ∈ PROC ∧
        		pp ∉ proc ∧
		ii1 ∈ NAT1 ∧
		ii1 ∉ PID ∧
		ii2 ∈ NAT1 ∧
		ii2 ∉ MID ∧
		cur_mode = NU ∧
        		mm ∈ MEM ∧
        		mm ∉ mem ∧
		ac_flag=0 ∧
		ac_policy_flag = 0 ∧
		ac_flag =0
    	THEN
		ANY
			mm1
		WHERE
			mm1 ∈ mem ∧
			mtag(mm1)=TS_tag 		//ensure that the environment is initialized
		THEN
        			Create_Proc(pp,ii1,Ready,Pre) ||
        			ready_procs := ready_procs ∪ {pp} ||
        			Add_Mem(mm,ii2,N_tag) ||
        			proc_mem:=proc_mem ∪ {pp ↦ mm}||
        		 	Create_Update_Policy 
		END
    	END;

	Quit_Proc(pp) =					//delete the process from all sets
    	PRE 
		pp ∈ proc ∧
		ac_flag = 0 ∧
        		pp ∈ blocked_proc ∧
		exe_state(pp) = Final ∧
		pmode(pp) = NU ∧
		cur_mode = NU
    	THEN
        		Del_Mem(proc_mem[{pp}] ∪ load_mem)||
		IF
			ran({pp} ◁ proc_entry) ≠ {}
		THEN
			entry := entry - ran({pp} ◁ proc_entry) ||
			entry_mem := ran( {pp} ◁ proc_entry) ◀ entry_mem ||
			proc_entry := {pp} ◀ proc_entry||
			eid := eid - ran(ecb_mem⁻¹[entry_mem[proc_entry[{pp}]]] ◁ ecb_eid) ||
			ecb_state := ecb_mem⁻¹[entry_mem[proc_entry[{pp}]]] ◀ ecb_state||
			ecb_eid := ecb_mem⁻¹[entry_mem[proc_entry[{pp}]]] ◀ ecb_eid||
			ecb_mem := ecb_mem⁻¹[entry_mem[proc_entry[{pp}]]] ◀ ecb_mem||
			ecb := ecb -	ecb_mem⁻¹[entry_mem[proc_entry[{pp}]]]
		END ||
		load_mem := {}||
		blocked_proc := blocked_proc -{pp}||
		Del_Proc(pp)||
		proc_mem:={pp} ◀ proc_mem ||
		proc_ac_mem := {pp} ◀ proc_ac_mem 
    	END;

	Judge_Ac_Policy(pp,mm,ac)=//the process and the memory that it want to access
    	PRE	
		pp ∈ proc ∧
		pp ∈ ready_procs ∪ run_proc ∧
		mm ∈ mem ∧
		ac ∈ {Write,Read,Exec,Leave,Enter} ∧
		ac_policy_flag = 0 ∧
		ac_flag =0 ∧
		ac_service = 0 ∧
		pp ↦ mm ∉ proc_ac_mem ∧
		ac_event = Null ∧
		pmode(pp) = cur_mode ∧
		exe_state(pp) ≠ Final ∧
		next_mem = {} ∧
		load_mem = {} ∧
		ran({pp} ◁ proc_next_mem) = {}
    	THEN
		IF 
			ac ∈ {Read,Write,Exec} ∧
			pmode(pp) ↦ mtag(mm) ↦ ac ∈ ac_policy ∧//the same process
			pmode(pp) ∈ {NU,TU} ∧
			mm ∈ ran({pp} ◁ proc_mem)  // mpu isolation
		THEN
			ac_policy_flag := 1 ||
			ac_event :=ac ||
			next_mem :=  {pp ↦ mm}
		ELSIF
			ac ∈ {Read,Write,Exec} ∧
			pmode(pp) ↦ mtag(mm) ↦ ac ∈ ac_policy ∧//the same process
			pmode(pp) ∈ {NS,TS,MM} 
		THEN
			ac_policy_flag := 1 ||
			ac_event :=ac ||
			next_mem :=  {pp ↦ mm}
		ELSIF	//from NN enter TC by process 
			ac = Enter	∧
			pmode(pp) = NU ∧
			mm ∈ ran({pp} ◁ proc_mem) ∧
			mtag(mm) = TC_tag∧
			∃ mm1.( mm1 ∈ ran({pp} ◁ proc_mem) ∧ mtag(mm1) = TU_tag)
		THEN	
			ac_policy_flag := 1 ||
			ac_event := ac ||
			next_mem :=  {pp ↦ mm}
		ELSIF	//from TU enter NN by process 
			ac = Leave	∧
			pmode(pp) = TU ∧
			mm ∈ ran({pp} ◁ proc_mem) ∧
			mtag(mm) = N_tag
		THEN
			ac_policy_flag := 1 ||
			ac_event := ac ||
			next_mem :=  {pp ↦ mm}
		ELSIF	//from NN enter TC by kernel 
			ac = Enter	∧
			pmode(pp) = NS ∧
			mm ∉ ran(proc_mem) ∧
			mtag(mm) = TC_tag ∧
			∃ mm2.( mm2 ∈ mem ∧ mtag(mm2) = TS_tag)
		THEN
			ac_policy_flag := 1 ||
			ac_event :=ac ||
			next_mem :=  {pp ↦ mm}
		ELSIF	//from TS enter NN by kernel 
			ac = Leave	∧
			pmode(pp) = TS ∧
			TS_flag = {1} ∧
			mm ∉ ran(proc_mem) ∧
			mtag(mm) = N_tag 
			
		THEN
			ac_policy_flag := 1 ||
			ac_event := ac ||
			next_mem :=  {pp ↦ mm}
		ELSE
			Change_Proc_Mode(pp,NU) ||
			cur_mode := NU ||
			Change_Proc_State(pp,Final,Post)||
			IF
				{pp} ◁ proc_ac_mem ≠ {}
			THEN
				Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
			END||
			proc_next_mem := {pp} ◀ proc_next_mem||
			proc_ac_mem := {pp} ◀ proc_ac_mem ||
			ready_procs := ready_procs -{pp} ||
			run_proc := run_proc -{pp} ||
			blocked_proc := blocked_proc ∪ {pp} 
		END	
    	END;
		
	Tag_Update(pp,mm,tt) =
	PRE
		pp ∈ run_proc  ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		mm ∈ mem ∧
		tt ∈ TAG	∧
		mstatus(mm) = Free ∧
		pmode(pp) ↦ mtag(mm) ∈ up_policy ∧
		pmode(pp) ↦ tt ∈ up_policy
	THEN
		IF
			pmode(pp) = NU ∧
			mm ∈  proc_mem[{pp}]
		THEN
			Tag_Updating(mm,tt)
		ELSIF
			pmode(pp) = NS ∧
			mm ∉ ran(proc_mem)
		THEN
			Tag_Updating(mm,tt)	
		ELSIF
			pmode(pp) ∈ {TU,TS} ∧
			mtag(mm) ≠ tt ∧
			mm ∈  proc_mem[{pp}]∧
			mtag(mm) ∈ {N_tag,TU_tag} ∧
			tt ∈ {N_tag,TU_tag}  
		THEN
			IF
				mtag(mm) = N_tag∧ 				//NU-->TU
				tt = TU_tag  
			THEN
				ANY
					ee
				WHERE
					ee ∈ ENTRY ∧
			            		ee ∉ entry
				THEN
					entry := entry ∪ {ee} ||
					entry_mem := entry_mem ∪  { ee ↦ mm} ||
					proc_entry := proc_entry ∪ { pp ↦ ee}
				END ||
				Tag_Updating(mm,tt)
			ELSIF
				mtag(mm) = TU_tag∧ 				//NU-->TU
				tt = N_tag
			THEN
				Tag_Updating(mm,tt) ||
				entry_mem := entry_mem ▶ {mm} ||
				proc_entry := proc_entry ▶ entry_mem⁻¹[{mm}]||
				entry := entry - entry_mem⁻¹[{mm}]
			END
		ELSIF
			pmode(pp) = TS ∧
			mtag(mm) ≠ TC_tag 
		THEN
			IF
				mtag(mm) = N_tag ∧//N_tag --> TS_tag
				mm ∈  proc_mem[{pp}]∧
				tt = TS_tag
			THEN
				proc_mem := proc_mem - {pp ↦ mm}||
				Tag_Updating(mm,tt) 
			ELSIF
				mtag(mm)=TU_tag ∧
				tt = TS_tag ∧
				mm ∈  proc_mem[{pp}]
			THEN
				proc_mem := proc_mem - {pp ↦ mm}||
				Tag_Updating(mm,tt) ||
				entry_mem := entry_mem ▶ {mm} ||
				proc_entry := proc_entry ▶ entry_mem⁻¹[{mm}]||
				entry := entry - entry_mem⁻¹[{mm}]
			ELSIF
				mtag(mm)=N_tag ∧
				tt = TS_tag ∧
				mm ∈ proc_mem[{pp}]
			THEN
				Tag_Updating(mm,tt)||
				proc_mem := proc_mem - {pp ↦ mm}
			END
		END
	END;

 	Judge_Status(pp,mm) =
 	PRE
		pp ∈ proc ∧
		exe_state(pp) ∈ {Ready,Run,Blocked} ∧
		pmode(pp) =cur_mode ∧
		ac_flag = 0 ∧
		ac_policy_flag = 1 ∧
		mm ∈ mem ∧
		pp ↦ mm ∈ next_mem
	THEN
		IF
			mstatus(mm) = Free
		THEN
			ready_procs := ready_procs -{pp} ||
			run_proc := run_proc ∪ {pp} ||
			blocked_proc := blocked_proc - {pp} ||
			ac_flag := 1 ||
			Change_Proc_State(pp,Run,Acing) ||
			proc_next_mem(pp) := next_mem(pp) ||
			next_mem := {}
		ELSE
			ready_procs := ready_procs -{pp} ||
			run_proc := run_proc - {pp}||
			blocked_proc := blocked_proc ∪ {pp}||
			Change_Proc_State(pp,Blocked,Wait)||
			proc_next_mem := {pp} ◀ proc_next_mem||
			proc_ac_mem := {pp} ◀ proc_ac_mem 
		END
	END;

	Proc_Ac_Mem(pp)=
	PRE
		pp ∈ proc ∧
		pp ∈ run_proc ∧
		ac_event ∈ {Write,Read,Exec} ∧
		pmode(pp) = cur_mode ∧
		ac_flag = 1 ∧
		ac_policy_flag = 1 ∧
		{pp} ◁ proc_next_mem ≠ {}
	THEN		
		   
		ac_flag := 0 ||
		ac_policy_flag := 0 ||
		IF
			{pp} ◁ proc_ac_mem ≠ {}∧ {pp} ◁ proc_next_mem ≠ {} ∧ ac_event : {Write,Exec}
		THEN
			Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)||
			proc_ac_mem(pp) := proc_next_mem(pp)
		ELSIF
			{pp} ◁ proc_ac_mem = {}∧ {pp} ◁ proc_next_mem ≠ {} 	∧ ac_event : {Write,Exec}
		THEN
			Change_Mem_Status(proc_next_mem(pp),Full,proc_next_mem(pp),Full)||
			proc_ac_mem(pp) := proc_next_mem(pp)						
		END||
		proc_next_mem := {pp} ◀ proc_next_mem ||
		ac_event := Null 		
	END;

	Quit_Ac_Mem(pp) =
	PRE
		pp ∈ run_proc ∧
		{pp} ◁ proc_ac_mem ≠ {} ∧

		ac_policy_flag = 0 ∧
		ac_flag =0 ∧
		ac_event = Null ∧
		pmode(pp) =cur_mode ∧
		TS_flag={}
	THEN
		proc_ac_mem := {pp} ◀ proc_ac_mem ||
		Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
	END;
    	
	Syscall(pp)=
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = NU ∧
		pmode(pp) =cur_mode ∧
		ac_event = Null ∧
		ac_flag= 0 ∧
		ac_policy_flag = 0 
    	THEN
       
           		Change_Proc_Mode(pp,NS) ||
		cur_mode := NS ||
		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END||
			proc_ac_mem := {pp} ◀ proc_ac_mem		
    	END;

    	Syscall_Exit(pp)=
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = NS ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		pmode(pp) =cur_mode
    	THEN
           		Change_Proc_Mode(pp,NU) ||
		cur_mode := NU ||	
           		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END||
			proc_ac_mem := {pp} ◀ proc_ac_mem
    	END;

	TSyscall(pp) =
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧ 
        		pmode(pp) = TU ∧
		cur_mode = pmode(pp) ∧
		ac_event = Null ∧
		TS_flag = {} ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 
    	THEN        
            		Change_Proc_Mode(pp,TS) ||
		cur_mode := TS ||
		TS_flag := {0} ||
		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END||
			proc_ac_mem := {pp} ◀ proc_ac_mem 
    	END;

    	TSyscall_Exit(pp)=
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = TS ∧
		pmode(pp) = cur_mode ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		TS_flag = {0}
    	THEN
            		Change_Proc_Mode(pp,TU)||
		cur_mode := TU ||
	    	TS_flag := {} ||
		IF
		{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END||
			proc_ac_mem := {pp} ◀ proc_ac_mem 
    	END;

	TUenter(pp) =
    	PRE
        		pp ∈ proc ∧
        		pmode(pp) = NU ∧
		pmode(pp) =cur_mode ∧
        		pp ∈ run_proc ∧
		ac_flag = 1 ∧
		ac_policy_flag = 1 ∧
		ac_event = Enter ∧
		proc_next_mem(pp) ∈ ran( {pp} ◁ proc_mem ) ∧
        		mtag(proc_next_mem(pp)) = TC_tag
    	THEN
        		ANY 
            			mm1 
        		WHERE
            			mm1 ∈ ran({pp} ◁ proc_mem) ∧
            			mtag(mm1) = TU_tag 
        		THEN
                			Change_Proc_Mode(pp,TU)	||
			cur_mode := TU ||
			IF
				{pp} ◁ proc_ac_mem  ≠ {}
			THEN
           				Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)
			ELSE
				Change_Mem_Status(proc_next_mem(pp),Full,proc_next_mem(pp),Full)
			END||
			proc_ac_mem(pp) := proc_next_mem(pp) ||
			proc_next_mem(pp) := mm1  ||
			ac_flag := 0 ||
			ac_policy_flag := 0
        		END
    	END;

    	TU_Ac(pp,ee) =
    	PRE
        		pp ∈ proc ∧
        		pmode(pp) = TU ∧
		pmode(pp) = cur_mode ∧
        		pp ∈ run_proc ∧
		ac_event = Enter ∧
		proc_ac_mem(pp) ∈ ran({pp} ◁ proc_mem) ∧
		ee ∈ entry ∧
		ee ∈ proc_entry[{pp}] ∧
		mtag(proc_ac_mem(pp)) = TC_tag ∧
        		entry_mem(ee) = proc_next_mem(pp) ∧
        		mtag(entry_mem(ee)) = TU_tag ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 
		
    	THEN
		ac_flag := 0 ||
        		Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)||
		proc_ac_mem(pp) := proc_next_mem(pp) ||
		proc_next_mem := {pp} ◀ proc_next_mem||
		ac_event := Null
    	END;

    	TUleave(pp) =
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = TU ∧
		pmode(pp) = cur_mode ∧
		ac_event = Leave ∧
		ac_flag = 1 ∧
		ac_policy_flag = 1
    	THEN
        		Change_Proc_Mode(pp,NU) ||
		cur_mode := NU ||
        		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)
		ELSE
			Change_Mem_Status(proc_next_mem(pp),Full,proc_next_mem(pp),Full)
		END||
		proc_ac_mem(pp) := proc_next_mem(pp) ||
		proc_next_mem := {pp} ◀ proc_next_mem ||
		ac_flag := 0 ||
		ac_policy_flag := 0 ||
		ac_event := Null    
    	END;

	TSenter(pp) = 
    	PRE			//from S-mode to TS-mode
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = NS ∧	
		pmode(pp) = cur_mode ∧
		ac_event = Enter ∧
		ac_flag = 1 ∧
		ac_policy_flag = 1 ∧
		proc_mem⁻¹[{proc_next_mem(pp)}] = {} ∧
        		mtag(proc_next_mem(pp)) = TC_tag
    	THEN
		ANY
            			mm1
        		WHERE
            			mm1 ∈ mem ∧
            			mtag(mm1) = TS_tag ∧
	    		mstatus(mm1) = Free
		THEN
        			Change_Proc_Mode(pp,TS) ||
			cur_mode := TS ||
        			IF
			{pp} ◁ proc_ac_mem  ≠ {}
			THEN
           				Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)
			ELSE
				Change_Mem_Status(proc_next_mem(pp),Full,proc_next_mem(pp),Full)
			END||
			proc_ac_mem(pp) := proc_next_mem(pp)||
			proc_next_mem(pp) := mm1	||
			ac_flag := 0 ||
			ac_policy_flag := 0
        		END
    	END;

    	TS_Ac(pp) =
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = TS ∧
		pmode(pp) = cur_mode ∧
		ac_event = Enter ∧
		proc_mem⁻¹[{proc_ac_mem(pp)}] = {} ∧
		mtag(proc_ac_mem(pp)) = TC_tag ∧
		proc_mem⁻¹[{proc_next_mem(pp)}] = {} ∧
        		mtag(proc_next_mem(pp)) = TS_tag ∧
		mstatus(proc_next_mem(pp)) = Free ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0
    	THEN
		ac_event := Null ||
        		TS_flag := {1} ||
		Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)||
		proc_ac_mem(pp) := proc_next_mem(pp)||
		proc_next_mem := {pp} ◀ proc_next_mem
    	END;

    	TSleave(pp)=
    	PRE
        		pp ∈ proc ∧
        		pp ∈ run_proc ∧
        		pmode(pp) = TS ∧
		pmode(pp) = cur_mode ∧
		ac_event = Leave ∧
		ac_flag = 1 ∧
		TS_flag = {1} ∧
		ac_policy_flag = 1 
    	THEN
        		Change_Proc_Mode(pp,NS) ||
		cur_mode := NS ||
		TS_flag := {}||
		ac_flag := 0||
		ac_policy_flag := 0 ||
		ac_event := Null ||
		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_next_mem(pp),Full)
		ELSE
			Change_Mem_Status(proc_next_mem(pp),Full,proc_next_mem(pp),Full)
		END||
		IF
			load_mem	≠ {}
		THEN
			ANY
				mm
			WHERE
				mm : load_mem ∧
				mtag(mm) = TU_tag
			THEN
				entry := entry - {entry_mem⁻¹(mm)} ||
				entry_mem := {entry_mem⁻¹(mm)} ◀ entry_mem ||
				eid := eid - {ecb_eid(ecb_mem⁻¹(mm))} ||
				ecb_state := {ecb_mem⁻¹(mm)} ◀ ecb_state||
				ecb_eid := {ecb_mem⁻¹(mm)} ◀ ecb_eid||
				ecb_mem := {ecb_mem⁻¹(mm)} ◀ ecb_mem||
				ecb := ecb -	{ecb_mem⁻¹(mm)} ||
				load_mem := {}
			END
		END
		 ||
		proc_ac_mem(pp) := proc_next_mem(pp) ||
		proc_next_mem := {pp} ◀ proc_next_mem
    	END;

	Menter(pp) =
	PRE
	    pp ∈ proc ∧
		pmode(pp) ∈ {NU,NS,TU,TS} ∧
		cur_mode = pmode(pp) ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		{pp} ◁ proc_ac_mem = {} ∧
		ac_service = 0
	THEN
		Change_Proc_Mode(pp,MM) ||
		cur_mode := MM ||
		enter_mode := pmode(pp)||
		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END ||
		proc_ac_mem := {pp} ◀ proc_next_mem 
	END;

	Mleave(pp,mode) =
	PRE
	    pp ∈ proc ∧
		mode = enter_mode ∧
		cur_mode = pmode(pp) ∧
		cur_mode = MM ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		{pp} ◁ proc_ac_mem = {} 
	THEN
		Change_Proc_Mode(pp,mode) ||
		cur_mode := mode ||
		IF
			{pp} ◁ proc_ac_mem  ≠ {}
		THEN
           			Change_Mem_Status(proc_ac_mem(pp),Free,proc_ac_mem(pp),Free)
		END||
		proc_ac_mem := {pp}  ◀ proc_next_mem 
	END;
			
    	/*Trusted OS services*/
    	Create_Enclave(ee)=
    	PRE 
        		ee ∈ ECB ∧
        		ee  ∉ ecb ∧
        		cur_mode = TS ∧
		TS_flag = {1} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		load_mem = {}∧
		card(mem) <= 7 //防止内存不足
    	THEN
        		ANY
            			pp,ii
        		WHERE
            			ii ∈ EID ∧
            			ii ∉ eid ∧
			pmode(pp) = cur_mode ∧
	    		pp ∈ run_proc ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag ∧
			card( ran({pp} ◁ proc_mem)) = 1
        		THEN
			ac_service := 1 ||
            			ecb := ecb ∪ {ee} ||
            			eid := eid ∪{ii} ||
            			ecb_eid :=ecb_eid ∪ {ee ↦ ii} ||
			ecb_state := ecb_state ∪{ ee ↦ unrunable} 
        		END 
    	END;

    	Add_Region(ee,mm)=
    	PRE
        		ee ∈ ecb ∧
        		mm ∈ MEM ∧
        		mm ∉ mem ∧
        		cur_mode = TS ∧
		TS_flag = {1} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		card(load_mem) = 0 ∧
		ecb_state(ee) = unrunable ∧
		load_mem = {} ∧
		ac_policy_flag = 0 ∧
		ac_service = 1
    	THEN
		ANY 
            			pp
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag
        		THEN
            			ecb_mem := ecb_mem ⋖ {ee ↦ mm} ||
			load_mem := load_mem ∪ {mm}		
		END
    	END;

    	Add_Data(ee,mm) =
   	PRE
        		ee ∈ ecb ∧
        		mm ∈ MEM ∧
		mm ∉ mem ∧
        		ecb_mem(ee) = mm ∧
        		cur_mode = TS ∧
		ecb_state(ee) = unrunable ∧
		mm ∈ load_mem ∧
		TS_flag = {1} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 1
    	THEN
		ANY 
            			pp,ii
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
			ii ∈ NAT1 ∧
			ii ∉ MID ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag
        		THEN
            			Add_Mem(mm,ii,TU_tag) ||
			ac_flag := 1
		END                 
    	END;

    	Add_Entries(ee,entries)=
    	PRE
        		ee ∈ ecb ∧
        		entries ∈ ENTRY ∧
        		entries ∉ entry ∧
        		entry_mem⁻¹[{ecb_mem(ee)}] = {} ∧
		ecb_state(ee) = unrunable ∧
        		cur_mode = TS ∧
        		card(load_mem) = 1 ∧
		TS_flag = {1} ∧
		ac_event = Null ∧
		ac_flag = 1 ∧
		ac_policy_flag = 0 ∧
		ac_service = 1
    	THEN
        		ANY
            			pp,mm,ii
        		WHERE
            			mm ∈ MEM ∧
            			mm ∉ mem ∧
			pmode(pp) = cur_mode ∧
			ii ∈ NAT1 ∧
			ii ∉ MID ∧
            			pp ∈ run_proc ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag
        		THEN
            			Add_Mem(mm,ii,TC_tag)||
	    		ac_flag := 0 ||
            			load_mem := load_mem ∪ {mm} ||
			entry := entry ∪ {entries} ||
            			entry_mem(entries) := ecb_mem(ee)|| //point to the TU-tag memory
			proc_entry(pp) := entries
        		END 
    	END;

    	Init_Enclave(ee) =
    	PRE 
        		ee ∈ ecb ∧
        		ran({ee} ◁ ecb_mem) ⊆ mem ∧
        		{ee} ◁ ecb_mem ≠ {} ∧
        		ecb_state(ee) = unrunable ∧
        		cur_mode = TS ∧
		TS_flag = {1} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 1
    	THEN        
		ANY 
            			pp
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag
        		THEN
         		   	ecb_state(ee) := runable ||
			ac_service := 0	
		END
    	END;

   	Load_Enclave(ee) =
    	PRE
        		ee ∈ ecb ∧
        		ecb_mem(ee) ∈ mem ∧
        		ecb_state(ee) = runable ∧
        		cur_mode = TS ∧
		ac_event =Null ∧
		TS_flag={1} ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		load_mem ≠ {}
	THEN
        		ANY 
            			pp,mm,mm1,mm2,entries 
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
			mm ∈ ran({pp} ◁ proc_mem) ∧
			ecb_mem(ee) ∉ ran(proc_mem ) ∧
        	   		mtag(proc_ac_mem(pp)) = TS_tag ∧
            			mm1 ∈ load_mem ∧
            			mtag(mm1) = TC_tag ∧
            			mm2 ∈ load_mem ∧
            			mtag(mm2) = TU_tag ∧
            			entries ∈ entry_mem⁻¹[{ecb_mem(ee)}] 
        		THEN
            			IF 
                				mm ↦ TU_tag ∈ mtag
            			THEN
                				Del_Mem({mm})||
                				proc_mem := proc_mem ▶ {mm} ∪ {pp ↦ mm1} ∪ {pp ↦ mm2}||
				ecb_mem := ecb_mem ▶{mm}||
				entry_mem := entry_mem ▶{mm}||
				entry := entry - entry_mem⁻¹[{mm}] ||
				proc_entry := proc_entry ▶ entry_mem⁻¹[{mm}]
            			ELSE
                				proc_mem := proc_mem ∪ {pp ↦ mm1} ∪ { pp ↦ mm2}
            			END ||
            			load_mem:={}
        		END
    	END;

    	Resume(ee) =
    	PRE
        		ee ∈ ecb ∧
        		ecb_mem(ee) ∈ mem ∧
        		entry_mem⁻¹[{ecb_mem(ee)}] ≠ {} ∧
        		ecb_state(ee) = unrunable ∧
        		cur_mode = TS ∧
		TS_flag = {1} ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0
    	THEN
        		ANY 
            			pp
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag ∧
			ecb_mem(ee) ∈ ran({pp} ◁ proc_mem) 
        		THEN
            			ecb_state(ee) := runable
        		END
    	END;

    	Destroy_Enclave(ee) =
    	PRE
        		ee ∈ ecb ∧
        		ecb_mem(ee) ∈ mem ∧
        		ecb_state(ee) = runable ∧
        		cur_mode = TS ∧
		TS_flag = {1}∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		load_mem = {}
    	THEN
        		ANY 
            			pp,mm1,mm2
        		WHERE 
            			pp ∈ run_proc ∧
			pmode(pp)=cur_mode ∧
			mm1 ∈ ran({pp} ◁ proc_mem) ∧
			mtag(mm1) = TC_tag ∧
			mm2 ∈ ran({pp} ◁ proc_mem) ∧
			mtag(mm2) = TU_tag ∧
	    		mtag(proc_ac_mem(pp)) = TS_tag ∧
			ecb_mem(ee) ∈ ran({pp} ◁ proc_mem)
        		THEN 
            			proc_mem := proc_mem - {pp ↦ mm1, pp ↦ mm2} ||
            			Del_Mem({mm1,mm2}) ||
			proc_entry :={pp} ◀ proc_entry ||
            			entry_mem := proc_entry[{pp}] ◀ entry_mem ||
            			entry := entry - proc_entry[{pp}] ||
			ecb_eid := {ee} ◀ ecb_eid ||
			eid := eid - {ecb_eid(ee)}||
            			ecb_mem := {ee} ◀ ecb_mem ||
            			ecb_state := {ee} ◀ ecb_state ||
            			ecb := ecb - {ee}
        		END
    	END;

	Shm_Offer(targetEID,region)=
    	PRE
        		targetEID ∈ eid ∧
        		region ∈ mem ∧
        		mtag(region) = TU_tag ∧
        		cur_mode = TS ∧
		TS_flag = {0} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0
    	THEN
        		ANY
            			pp,ee
        		WHERE
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
            			region ∈ ran({pp} ◁ proc_mem) ∧
            			ee ∈ ecb_mem⁻¹[{region}] ∧
	    		ee ↦ targetEID ∉ shm_ecb_eid ∧
			targetEID ≠ ecb_eid(ee) ∧
	    		ee ↦ targetEID ∉ shm_ecb_eid
        		THEN
			ac_service := 1 || 
            			shm_ecb_eid := ecb_eid ∪ { ee ↦ targetEID} ||
           			load_mem :={region}
        		END    
    	END;

    	Shm_Accept(ownerEID) = // the eid of memory owner
    	PRE
        		ownerEID ∈ eid ∧
        		cur_mode = TS ∧
		TS_flag = {0} ∧
		ac_event = Null ∧
		card(load_mem) = 1 ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 1
    	THEN
        		ANY
            			pp,mm1,ee,ee1,region
        		WHERE
           	 		pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
			mtag(proc_ac_mem(pp))=TS_tag ∧
            			mm1 ∈ ran({pp} ◁ proc_mem) ∧
                			mtag(mm1)=TU_tag ∧
                			ee ∈ ecb_mem⁻¹[{mm1}] ∧ //the ecb of current process
         	      		ee1 ∈ ecb_eid⁻¹[{ownerEID}] ∧
			ee ≠ ee1 ∧
			ee1 ↦ ecb_eid(ee) ∈ shm_ecb_eid ∧
			region ∈ load_mem
        		THEN
                			proc_mem:= proc_mem ∪ {pp ↦ region}||
			shm_ecb_mem := shm_ecb_mem ∪ {ee ↦ region}||
			load_mem := {} ||
			ac_service := 0	
        		END
    	END;

    	Shm_Release(region)=
    	PRE
        		cur_mode =TS ∧
		TS_flag = {0} ∧
		ac_event = Null ∧
		ac_flag = 0 ∧
		ac_policy_flag = 0 ∧
		ac_service = 0 ∧
		region ∈ ran(proc_mem)
    	THEN
        		ANY
            			ee,ee1,pp
        		WHERE
            			pp ∈ run_proc ∧
			pmode(pp) = cur_mode ∧
            			region ∈ ran({pp} ◁ proc_mem) ∧
			mtag(region) = TU_tag ∧
			mtag(proc_ac_mem(pp)) = TS_tag ∧
			ee ∈ ecb_mem⁻¹[{region}] ∧
			ee1 ∈ shm_ecb_mem⁻¹[{region}] ∧
			ee ≠ ee1 
        		THEN
            			proc_mem := proc_mem -{pp ↦ region} ||
            			shm_ecb_eid := shm_ecb_eid - {ee1 ↦ ecb_eid(ee)}||
            			shm_ecb_mem := shm_ecb_mem - {ee1 ↦ region}
        		END
    	END
    
	/*Attack1(pp,mm,ac)=
    	PRE
        		pp ∈ run_proc ∧
                mm ∈ mem ∧
        		pmode(pp) = NU ∧
		ac = Write ∧
                pmode(pp) = cur_mode ∧
                mtag(mm) = TU_tag ∧
                mm ∈ ran({pp} ◁ proc_mem)
    	THEN
     		proc_ac_mem(pp) :=mm
    	END*/
    	
	/*Attack2(pp,mm)=
	PRE
		pp ∈ run_proc ∧
		pmode(pp) = TU ∧
		mtag(mm) = TU_tag ∧
		mm ∈ ran(proc_mem) ∧
		mm ∉ ran({pp} ◁ proc_mem) 
	THEN
		proc_ac_mem(pp) := mm 
	END*/
		
END

	

