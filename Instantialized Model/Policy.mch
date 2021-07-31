/* Policy
 * Author: Veronica
 * Creation date: 2021/5/20
 */
MACHINE
    Policy
SEES
    Mem,Proc
SETS
    OP = {Write,Read,Exec,Leave,Enter,Null} //memory accesses types
VARIABLES
    ac_policy,up_policy
INVARIANT
    ac_policy ⊆ MODE * TAG * OP &
    up_policy ⊆ MODE * TAG 
INITIALISATION
    ac_policy,up_policy := {},{}
OPERATIONS
    Create_Ac_Policy =    //the isolation policy in N-domain
    BEGIN
        ac_policy := ac_policy ∪ {NU ↦ N_tag ↦ Write}
                 ∪ {NU ↦ N_tag ↦ Read} 
                 ∪ {NU ↦ N_tag ↦ Exec}
 		 ∪ {NU ↦ TC_tag ↦ Enter}
                 ∪ {NS ↦ N_tag ↦ Write}
                 ∪ {NS ↦ N_tag ↦ Read}
                 ∪ {NS ↦ N_tag ↦ Exec} 
                 ∪ {NS ↦ TC_tag ↦ Enter}
                 ∪ {TU ↦ N_tag ↦ Write}//the isolation policy in TU-mode
                 ∪ {TU ↦ N_tag ↦ Read} 
                 ∪ {TU ↦ N_tag ↦ Leave} 
                 ∪ {TU ↦ TC_tag ↦ Read}
                 ∪ {TU ↦ TC_tag ↦ Exec}
                 ∪ {TU ↦ TU_tag ↦ Write}
                 ∪ {TU ↦ TU_tag ↦ Read} 
                 ∪ {TU ↦ TU_tag ↦ Exec}
                 ∪ {TS ↦ N_tag ↦ Write}//the isolation policy in TS-mode
                 ∪ {TS ↦ N_tag ↦ Read} 
                 ∪ {TS ↦ N_tag ↦ Leave} 
                 ∪ {TS ↦ TC_tag ↦ Read}
                 ∪ {TS ↦ TC_tag ↦ Exec}
                 ∪ {TS ↦ TC_tag ↦ Write}
                 ∪ {TS ↦ TU_tag ↦ Write}
                 ∪ {TS ↦ TU_tag ↦ Read} 
                 ∪ {TS ↦ TS_tag ↦ Write}
                 ∪ {TS ↦ TS_tag ↦ Read} 
                 ∪ {TS ↦ TS_tag ↦ Exec}
		 ∪ {MM ↦ N_tag ↦Write}
                 ∪ {MM ↦  N_tag ↦ Read} 
                 ∪ {MM ↦ N_tag ↦ Exec}
		 ∪ {MM ↦ TC_tag ↦ Write}
                 ∪ {MM ↦ TC_tag ↦ Read} 
                 ∪ {MM ↦ TC_tag ↦ Exec}
		 ∪ {MM ↦ TU_tag ↦ Write}
                 ∪ {MM ↦ TU_tag ↦ Read} 
                 ∪ {MM ↦ TU_tag ↦ Exec}
		 ∪ {MM ↦ TS_tag ↦ Write}
                 ∪ {MM ↦ TS_tag ↦ Read} 
                 ∪ {MM ↦ TS_tag ↦ Exec}
    END;

    Create_Update_Policy =    //the isolation policy in N-domain
    BEGIN
        up_policy := up_policy ∪ {NU ↦ N_tag }
                 ∪ {NS ↦ N_tag}         
                 ∪ {TU ↦ N_tag}//the isolation policy in TU-mode                 
                 ∪ {TU ↦ TU_tag }
                 ∪ {TS ↦ N_tag }//the isolation policy in TS-mode
		 ∪ {TS ↦ TC_tag }
                 ∪ {TS ↦ TU_tag }
                 ∪ {TS ↦ TS_tag }
		 ∪ {MM ↦ N_tag }
		 ∪ {MM ↦ TC_tag }
		 ∪ {MM ↦ TU_tag }
		 ∪ {MM ↦ TS_tag }
    END

END
